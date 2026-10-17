from datetime import timedelta
import unittest
from unittest.mock import patch

from test_idle_monitoring import solar, SUNSET
from miner_power_guard import MinerPowerGuard, PowerSample


class SolarPollingTests(unittest.TestCase):
    def test_daylight_five_minutes_and_night_half_hour(self):
        dawn = SUNSET-timedelta(hours=12)
        with patch.object(solar,'_weather_daylight',(dawn,SUNSET)):
            self.assertEqual(solar._solarman_poll_slot(dawn,dawn,SUNSET)[0],300)
            self.assertEqual(solar._solarman_poll_slot(SUNSET-timedelta(seconds=1),dawn,SUNSET)[0],300)
            self.assertEqual(solar._solarman_poll_slot(SUNSET,dawn,SUNSET)[0],1800)
            self.assertEqual(solar._solarman_poll_slot(dawn-timedelta(seconds=1),dawn,SUNSET)[0],1800)

    def test_twenty_four_hours_cost_144_day_and_24_night_reads(self):
        dawn = SUNSET-timedelta(hours=12)
        slots=[]
        last_slot=last_attempt=None
        with patch.object(solar,'_weather_daylight',(dawn,SUNSET)):
            for i in range(24*12):
                now=dawn.replace(hour=0)+timedelta(minutes=5*i)
                slot=solar._solarman_poll_slot(now,dawn,SUNSET)
                if solar._solarman_poll_due(now,slot,last_slot,last_attempt):
                    slots.append(slot)
                    last_slot,last_attempt=slot,now
        self.assertEqual(sum(interval==300 for interval,bucket in slots),144)
        self.assertEqual(sum(interval==1800 for interval,bucket in slots),24)

    def test_repeated_cycle_does_not_create_another_slot(self):
        with patch.object(solar,'_weather_daylight',None):
            slots=[solar._solarman_poll_slot(SUNSET+timedelta(minutes=m),SUNSET-timedelta(hours=12),SUNSET)
                   for m in (1,6,11,16,21,26,31)]
        self.assertEqual(len(set(slots)),2)

    def test_sunset_and_half_hour_boundary_do_not_bypass_night_rate_limit(self):
        previous=SUNSET-timedelta(minutes=1)
        last_slot=(300,int(previous.timestamp())//300)
        for minute in (0,1,5,15,28):
            now=SUNSET+timedelta(minutes=minute)
            slot=(1800,int(now.timestamp())//1800)
            self.assertFalse(solar._solarman_poll_due(now,slot,last_slot,previous))
        now=SUNSET+timedelta(minutes=29)
        self.assertTrue(solar._solarman_poll_due(now,(1800,int(now.timestamp())//1800),last_slot,previous))

    def test_actual_sunset_not_early_production_stop_sets_cadence(self):
        dawn=SUNSET-timedelta(hours=12)
        stop=SUNSET-timedelta(minutes=90)
        with patch.object(solar,'_weather_daylight',(dawn,SUNSET)):
            self.assertEqual(solar._solarman_poll_slot(stop+timedelta(minutes=30),dawn,stop)[0],300)
            self.assertEqual(solar._solarman_poll_slot(SUNSET,dawn,stop)[0],1800)

    def test_half_hour_guard_stops_on_first_fresh_match_without_reusing_old_data(self):
        guard=MinerPowerGuard()
        for minute in (0,30,60):
            at=SUNSET+timedelta(minutes=minute)
            off=PowerSample(at,400,100,100,200)
            guard.observe(off,at,'stop',poll_interval_seconds=1800)
        guard.command_start(off,off.at+timedelta(seconds=1))
        self.assertIsNotNone(guard.started)
        for minute in (90,120):
            at=SUNSET+timedelta(minutes=minute)
            guard.observe(PowerSample(at,1200,100,550,550),at,'production',poll_interval_seconds=1800)
        self.assertIsNotNone(guard.signature)
        results=[]
        for minute in (150,180,210):
            at=SUNSET+timedelta(minutes=minute)
            results.append(guard.observe(PowerSample(at,1200,100,550,550),at,'stop',poll_interval_seconds=1800))
        self.assertEqual(results,[True,True,False])

    def test_half_hour_cadence_does_not_make_half_hour_old_samples_fresh(self):
        guard=MinerPowerGuard()
        sample=PowerSample(SUNSET,1200,100,550,550)
        self.assertFalse(guard.observe(sample,SUNSET+timedelta(minutes=30),'stop',poll_interval_seconds=1800))
        self.assertIsNone(guard.last_at)


if __name__=='__main__':
    unittest.main()
