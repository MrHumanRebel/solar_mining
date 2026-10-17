"""Telegram text from the same weekly reference/live plan shown in the GUI."""
from datetime import datetime
import math
from zoneinfo import ZoneInfo

LOCAL=ZoneInfo('Europe/Budapest')


def number(value,unit='',digits=0):
    try:
        value=float(value)
        return f'{value:.{digits}f}{unit}' if math.isfinite(value) else '—'
    except (ValueError,TypeError):
        return '—'


def stamp(value):
    try:
        at=datetime.fromisoformat(value) if isinstance(value,str) else value
        return at.astimezone(LOCAL).strftime('%Y.%m.%d. %H:%M')
    except (ValueError,AttributeError,TypeError):
        return '—'


def phases(snapshot):
    meter=snapshot.get('power_measurement')
    if not meter:
        return 'Fogyasztás: nincs érvényes fázismérés.\n'+str(snapshot.get('power_measurement_error') or '')
    source='Fogyasztás' if str(snapshot.get('power_measurement_source','')).startswith('consumption') else 'Inverterkimenet'
    return (f"{source}: L1 {number(meter.get('l1'),' W')} | L2 {number(meter.get('l2'),' W')} | "
            f"L3 {number(meter.get('l3'),' W')} | SUM {number(meter.get('total'),' W')}\n"
            f"Eszközmérés: {stamp(meter.get('at'))}"+(' · elavult' if not meter.get('fresh') else ''))


def status(snapshot,now,quote_used=None,quote_limit=None):
    hints=snapshot.get('historical_hints') or {}
    budget=hints.get('energy_budget') or {}
    week=snapshot.get('weekly_reference') or {}
    metrics=week.get('metrics') or {}
    cutoff=snapshot.get('afternoon_cutoff') or {}
    buffered=budget.get('projection_mode')=='surplus_buffer_run'
    physical=(snapshot.get('runtime') or {}).get('state','unknown')
    physical_label={'unknown':'ismeretlen','starting':'indítás ellenőrzésre vár','running':'ping elérhető',
                    'stop_pending':'leállítás ellenőrzésre vár','stop_failed':'leállítás nincs igazolva',
                    'stop_unverified':'leállítás nem ellenőrizhető','off':'ping nem elérhető'}.get(physical,physical)
    lines=[f"☀ Solar Mining · {stamp(now)}",
           f"Kívánt állapot: {((snapshot.get('runtime') or {}).get('desired_state') if (snapshot.get('runtime') or {}).get('desired_state') in ('stop','production') else snapshot.get('state','ismeretlen'))} · PV: {number(snapshot.get('power'),' W')} · Akku: {number(snapshot.get('battery'),'%')}",
           f"Fizikai állapot: {physical_label} · STOP kísérletek: {(snapshot.get('runtime') or {}).get('attempts',0)}/2",
           f"Ping cél: {(snapshot.get('runtime') or {}).get('target_ip','192.168.0.185')} · ellenőrzés: {stamp((snapshot.get('runtime') or {}).get('checked_at'))}",
           f"Időjárás: {snapshot.get('current_condition','—')}",
           f"Teljes miner tervezési fogyasztása: {number(snapshot.get('miner_power_w'),' W')} (becslés, nem konnektoros mérés)",
           f"Pool hashráta: {snapshot.get('hashrate_text') or '—'} (késhet; csak kijelzés)",
           '',phases(snapshot),'',
           f"📈 {week.get('week','—')}. heti referencia · évek: {', '.join(map(str,week.get('years',[]))) or '—'}",
           f"Napok: {week.get('days',0)} · egyedi mérések: {week.get('samples',0)} · javított kiugrások: {week.get('outlier_points',0)}",
           f"PV indulás: {metrics.get('production_start') or '—'} · maximum: {metrics.get('peak_time') or '—'} / {number(metrics.get('peak_w'),' W')}",
           f"Tipikus napi PV: {number(metrics.get('pv_energy_wh'),' Wh')} · görbelefedettség: {number(metrics.get('pv_coverage_hours'),' h',1)}",
           f"100% minerfedezet (ház nélkül): {metrics.get('miner_cover') or '—'}",
           f"Heti SOC min/max: {number(metrics.get('soc_min'),'%')} / {number(metrics.get('soc_max'),'%')} · töltés indulása: {metrics.get('charge_start') or '—'} · merülés: {metrics.get('discharge_start') or '—'}",
           '', '🔋 Élő bridge / futásterv',
           str(hints.get('decision_summary') or 'Még nincs friss vezérlési döntés.'),
           f"Bridge: {number(budget.get('required_bridge_wh'),' Wh')} szükséges / {number(budget.get('available_bridge_wh'),' Wh')} elérhető (a szükséges már tartalmazza a biztonsági ráhagyást)",
           f"Bridge időtartama: {number(budget.get('bridge_duration_minutes'),' perc',1)} · csak a mostantól a tartós PV-fedezetig tartó hiány",
           f"Indítás: {number(budget.get('startup_energy_wh'),' Wh')} · teljes indulási keret ráhagyással: {number(budget.get('required_start_energy_wh'),' Wh')}",
           f"Háztartási terhelési feltételezés: {number(budget.get('household_load_w'),' W')} · napnyugtai SOC bányászat nélkül: {'visszafogott PV-ből nem becsülhető' if buffered else number(budget.get('household_only_end_soc'),'%')}",
           f"Heti SOC-görbe szerinti bridge: {number(budget.get('historical_bridge_wh'),' Wh')} · csak kiegészítő becslés",
           f"Tartós PV-fedezet: {stamp(budget.get('cover_time'))} · tervezett leállás: {stamp(budget.get('planned_stop'))}",
           (f"Futás alatti minimum SOC: {number(budget.get('run_minimum_soc'),'%')} · napnyugtai SOC: visszafogott PV-ből nem becsülhető" if buffered else f"Minimum / záró SOC: {number(budget.get('minimum_soc'),'%')} / {number(budget.get('end_soc'),'%')}"),
           f"Háztartási éjszakai energiatartalék: {number(budget.get('reserve_soc'),'%')}"]
    if budget.get('projection_mode')=='surplus_buffer_run':
        lines += [f"Közel tele akku: korlátozott többletfutás, védett futásvégi SOC {number(budget.get('surplus_reserve_soc'),'%')}.",
                  f"Nulla PV-vel számolt futásvégi SOC: {number(budget.get('worst_case_stop_soc'),'%')} · keret {number(budget.get('required_surplus_wh'),' Wh')} / {number(budget.get('available_surplus_wh'),' Wh')}",
                  'Nincs visszatáplálás: tele akkunál a mért PV terhelésfüggő. A napnyugtai becslés külön, nem garantált tartalék; újraszámítás 5 percenként.']
    if budget.get('bridge_status')=='no_sustained_cover':
        lines.append('Nincs előre jelzett tartós PV-fedezet: bridge Wh nem számítható, a napi hiányt nem írjuk ide.')
    if budget and not budget.get('safe'):
        lines.append('Az előrejelzés elutasított futási forgatókönyv, nem jóváhagyott indítás.')
    lines += [f"Délutáni STOP: {cutoff.get('hour',14):02}:00 után, PV ≤ {number(cutoff.get('pv_w',50),' W')} és akku < {number(cutoff.get('soc',90),'%')}",
              'Ping ellenőrzés: '+str(snapshot.get('power_guard_reason') or '—')]
    if quote_used is not None:
        lines.append(f'API keret: {quote_used} / {quote_limit}')
    return '\n'.join(lines)
