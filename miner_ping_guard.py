"""Fixed-IP ICMP runtime checks. No power signature, pool rate or solar API calls."""
from datetime import timedelta
import ipaddress
import subprocess


def ping_host(address):
    """True = reply; False = no replies; None = probe/tool error, never OFF."""
    address=str(ipaddress.IPv4Address(address))
    try:
        result=subprocess.run(['ping','-n','-c','2','-i','0.2','-W','2',address],
                              capture_output=True,timeout=6,check=False)
    except (OSError,subprocess.TimeoutExpired):
        return None
    return True if result.returncode==0 else False if result.returncode==1 else None


class MinerPingGuard:
    MAX_SHUTDOWN_ATTEMPTS=2
    def __init__(self,address='192.168.0.185',mac='90:DE:80:BD:AD:BF'):
        self.address=str(ipaddress.IPv4Address(address))
        self.mac=mac
        self.desired_state='unknown'
        self.runtime_state='unknown'
        self.reachable=None
        self.checked_at=None
        self.shutdown_after=None
        self.shutdown_attempts=0
        self.shutdown_reserved=False
        self.confirmed_off_at=None
        self.start_after=None
        self.misses=0
        self.reason='Waiting for fixed-IP ping check'

    def set_desired(self,state,force=False):
        if state not in ('production','stop'):
            return False
        if state=='production' and not force and (self.shutdown_reserved or (self.shutdown_after and self.runtime_state!='off')):
            return False
        if state==self.desired_state:
            return True
        self.desired_state=state
        self.shutdown_attempts=0
        self.shutdown_after=None
        self.shutdown_reserved=False
        self.reason='Waiting for ping check for requested '+state
        return True

    def command_start(self,now):
        self.set_desired('production')
        self.start_after=now
        self.runtime_state='starting'
        self.confirmed_off_at=None
        self.misses=0
        self.reason='Start pulse sent; waiting for ping reply'

    def command_stop_finished(self,now,success=True):
        self.desired_state='stop'
        if not self.shutdown_reserved:
            self.shutdown_attempts+=1
        self.shutdown_reserved=False
        self.shutdown_after=now
        self.misses=0
        self.confirmed_off_at=None
        self.runtime_state='stop_pending' if success else 'stop_failed'
        self.reason='Long STOP sent; waiting for post-command pings' if success else 'Long STOP GPIO failed'

    def observe(self,reachable,now):
        self.checked_at=now
        self.reachable=reachable
        if reachable is None:
            self.misses=0
            self.runtime_state='stop_unverified' if self.desired_state=='stop' else 'unknown'
            self.reason='Ping tool/network error; no physical action or OFF confirmation'
            return False
        if not reachable:
            self.misses+=1
            if self.start_after and self.desired_state=='production' and now-self.start_after<timedelta(seconds=90):
                self.runtime_state='starting'
                self.reason='Waiting for boot ping reply'
            elif self.misses>=2:
                self.runtime_state='off'
                self.confirmed_off_at=now
                self.reason='Target unreachable in two consecutive ping checks (network confirmation only)'
            else:
                self.runtime_state='stop_pending' if self.desired_state=='stop' else 'unknown'
                self.reason='First unanswered ping check; awaiting confirmation'
            return False
        self.misses=0
        if self.confirmed_off_at is not None:
            # A host coming back while STOP remains requested is a new online episode.
            self.shutdown_attempts=0
            self.shutdown_after=None
            self.confirmed_off_at=None
        if self.desired_state!='stop':
            self.runtime_state='running'
            self.reason='Fixed-IP target replies to ping'
            return False
        if self.shutdown_after and now-self.shutdown_after<timedelta(seconds=30):
            self.runtime_state='stop_pending'
            self.reason='Waiting 30 seconds after long STOP before considering retry'
            return False
        if self.shutdown_attempts>=self.MAX_SHUTDOWN_ATTEMPTS:
            self.runtime_state='stop_failed'
            self.reason='Target still replies after two long STOP attempts; manual inspection required'
            return False
        self.shutdown_attempts+=1
        self.shutdown_reserved=True
        self.runtime_state='stop_pending'
        self.reason=f'Ping-online STOP authorized ({self.shutdown_attempts}/2)'
        return True

    def status(self,now):
        fresh=self.checked_at is not None and 0<=(now-self.checked_at).total_seconds()<=60
        return {'state':self.runtime_state if fresh else 'unknown','desired_state':self.desired_state,'reachable':self.reachable if fresh else None,
                'target_ip':self.address,'expected_mac':self.mac,'verification':'icmp_ping',
                'checked_at':self.checked_at.isoformat() if self.checked_at else None,
                'attempts':self.shutdown_attempts,'max_attempts':2,
                'last_command_at':self.shutdown_after.isoformat() if self.shutdown_after else None,
                'confirmed_off_at':self.confirmed_off_at.isoformat() if self.confirmed_off_at else None,
                'reason':self.reason if fresh else 'Ping status unavailable or older than 60 seconds'}
