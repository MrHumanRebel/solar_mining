"""Exercise the inverter-only schema reported by the deployed Pi."""
from dataclasses import replace
from pathlib import Path
import json
from datetime import datetime, timedelta, timezone
import unittest
from unittest.mock import patch
from simulate_decisions import solar
from test_miner_power_guard import armed_guard, sample

T = datetime(2026, 10, 16, 18, tzinfo=timezone.utc)


def payload(unit='W', total=1200, phases=(100,550,550)):
    scale=1000 if unit=='kW' else 1
    return {'collectionTime':int(T.timestamp()*1000), 'dataList':[
        {'key':'ESP_VER','value':'1.0'},
        {'key':'PV_D_P_G','value':'99','unit':'kWh'},
        {'key':'INV_O_P_T','value':str(total/scale),'unit':unit},
        *[{'key':f'INV_O_P_L{i}','value':str(v/scale),'unit':unit}
          for i,v in enumerate(phases,1)],
    ]}


class SolarmanPowerFieldTests(unittest.TestCase):
    def setUp(self):
        self.enterContext(patch.object(solar,'send_telegram_message'))
        self.enterContext(patch.object(solar,'send_telegram_message_async'))
        self.enterContext(patch.object(solar,'_last_power_notice_key',None))

    def test_reported_deye_schema_pairs_consumption_with_lpp_not_backup_load(self):
        data=json.loads((Path(__file__).parent/'tests/fixtures/solarman_deye_power.json').read_text())
        now=datetime.fromtimestamp(data['collectionTime'],timezone.utc)+timedelta(seconds=60)
        result,error=solar._parse_power_measurement(data,now)
        self.assertIsNone(error)
        self.assertEqual((result.total,result.l1,result.l2,result.l3),(1241,25,808,408))
        self.assertEqual(result.source,'consumption:LPP')
        self.assertIsNone(solar._power_measurement_reason(data,result,now))
        self.assertIn('old',solar._power_measurement_reason(data,result,now+timedelta(hours=5)))

    def test_reported_schema_flows_through_idle_monitor_and_dashboard(self):
        data=json.loads((Path(__file__).parent/'tests/fixtures/solarman_deye_power.json').read_text())
        now=datetime.fromtimestamp(data['collectionTime'],timezone.utc)+timedelta(seconds=60)
        with patch.object(solar,'_power_guard',solar.MinerPowerGuard()), \
             patch.object(solar,'_latest_power_sample',None), \
             patch.object(solar,'fetch_current_data',return_value=data), \
             patch.object(solar,'save_quote_usage'), patch.object(solar,'used_quote',0), \
             patch.object(solar,'is_rpi',False), patch.object(solar,'press_power_button') as press, \
             patch.dict(solar._shared_snapshot):
            from concurrent.futures import Future
            token=Future()
            token.set_result('test')
            solar._idle_monitor_cycle(now,token,None,None,poll_interval_seconds=1800)
            snapshot=solar._build_snapshot_payload()
            self.assertEqual(snapshot['power_measurement']['total'],1241)
            self.assertEqual(snapshot['power_measurement']['l2'],808)
            self.assertEqual(snapshot['inv_l2'],797)
            self.assertEqual(snapshot['power_measurement_source'],'consumption:LPP')
            self.assertNotIn('Missing',snapshot['power_guard_reason'])
            press.assert_not_called()

    def test_successful_read_clears_previous_measurement_error_without_rearming(self):
        data=payload()
        with patch.object(solar,'_power_guard',solar.MinerPowerGuard()), \
             patch.object(solar,'_power_measurement_error',None), \
             patch.object(solar,'_latest_power_sample',None), \
             patch.object(solar,'is_rpi',False):
            solar.supervise_runtime_by_power(T,'stop',{})
            self.assertIn('timestamp',solar._build_snapshot_payload()['power_guard_reason'])
            solar.supervise_runtime_by_power(T,'stop',data)
            self.assertEqual(solar._build_snapshot_payload()['power_guard_reason'],'No witnessed miner start')
            self.assertIsNone(solar._power_guard.signature)

    def test_e_puse_requires_explicit_power_units(self):
        data=payload()
        data['dataList'].append({'key':'E_Puse_t1','value':1200,'unit':None})
        result,error=solar._parse_power_measurement(data,T)
        self.assertIsNone(result)
        self.assertIn('requires explicit',error)

    def test_partial_lpp_never_mixes_with_backup_port_or_inverter_phases(self):
        data=json.loads((Path(__file__).parent/'tests/fixtures/solarman_deye_power.json').read_text())
        data['dataList']=[i for i in data['dataList'] if i['key']!='LPP_C']
        result,error=solar._parse_power_measurement(data,T)
        self.assertIsNone(result)
        self.assertIn('Incomplete consumption phases',error)

    def test_measurement_failures_have_specific_reasons(self):
        self.assertIn('timestamp',solar._power_measurement_reason({},None,T))
        data=payload()
        data['collectionTime']='broken'
        self.assertIn('Invalid device timestamp',solar._power_measurement_reason(data,None,T))
        self.assertIn('mismatch',solar._power_measurement_reason(payload(total=3000),None,T))
        data=payload()
        data['dataList'][2]['unit']='kWh'
        self.assertIn('Non-power unit',solar._power_measurement_reason(data,None,T))

    def test_inverter_total_and_matching_phases_are_valid_without_load_register(self):
        result=solar._extract_power_sample(payload(),T)
        self.assertEqual((result.total,result.l1,result.l2,result.l3),(1200,100,550,550))
        self.assertEqual(result.source,'inverter_output')

    def test_kw_is_converted_to_watts_for_total_and_all_phases(self):
        self.assertEqual(solar._extract_power_sample(payload('kW'),T).total,1200)

    def test_no_fabricated_total_from_phases_alone(self):
        data=payload()
        data['dataList']=[i for i in data['dataList'] if i['key']!='INV_O_P_T']
        self.assertIsNone(solar._extract_power_sample(data,T))

    def test_energy_register_is_not_instantaneous_load(self):
        data=payload()
        data['dataList']=[i for i in data['dataList'] if i['key']!='INV_O_P_T']
        data['dataList'].append({'key':'E_Puse_t1','value':1200,'unit':'kWh'})
        self.assertIsNone(solar._extract_power_sample(data,T))
        self.assertIsNone(solar._extract_power_sample(payload('kWh'),T))

    def test_explicit_load_takes_precedence_and_disagreement_does_not_fall_back(self):
        data=payload()
        data['dataList'].append({'key':'LOAD_P_T','value':3000,'unit':'W'})
        self.assertIsNone(solar._extract_power_sample(data,T))
        for item in data['dataList']:
            if item['key']=='LOAD_P_T':
                item['value']=1200
        self.assertEqual(solar._extract_power_sample(data,T).source,'consumption:INV_O_P')

    def test_invalid_values_missing_phases_and_disagreeing_sum_fail_closed(self):
        for bad in ('nan',-1,None):
            data=payload()
            data['dataList'][2]['value']=bad
            self.assertIsNone(solar._extract_power_sample(data,T))
        data=payload()
        data['dataList'].pop()
        self.assertIsNone(solar._extract_power_sample(data,T))
        self.assertIsNone(solar._extract_power_sample(payload(total=3000),T))
        self.assertIsNone(solar._extract_power_sample({'dataList':payload()['dataList']},T))

    def test_old_or_future_inverter_readings_never_authorize_gpio(self):
        for delta in (-600,60):
            data=payload()
            data['collectionTime']=(T+timedelta(seconds=delta)).timestamp()
            with patch.object(solar,'_power_guard',solar.MinerPowerGuard()), \
                 patch.object(solar,'is_rpi',True), patch.object(solar,'GPIO_AVAILABLE',True), \
                 patch.object(solar,'press_power_button') as press:
                solar.supervise_runtime_by_power(T,'stop',data)
                press.assert_not_called()

    def test_switching_meter_domains_disarms_existing_identity(self):
        guard=armed_guard()
        reading=replace(sample(25),source='inverter_output')
        self.assertFalse(guard.observe(reading,reading.at,'stop'))
        self.assertIsNone(guard.signature)

    def test_same_domain_inverter_signature_retains_one_reading_stop(self):
        guard=solar.MinerPowerGuard()
        for minute in (0,5,10):
            reading=replace(sample(minute,400,100,100,200),source='inverter_output')
            guard.observe(reading,reading.at,'stop')
        guard.command_start(reading,reading.at+timedelta(seconds=1))
        for minute in (15,20):
            reading=replace(sample(minute,1200,100,550,550),source='inverter_output')
            guard.observe(reading,reading.at,'production')
        reading=replace(sample(25),source='inverter_output')
        self.assertTrue(guard.observe(reading,reading.at,'stop'))
        reading=replace(sample(30),source='inverter_output')
        self.assertTrue(guard.observe(reading,reading.at,'stop'))

    def test_field_diagnostics_stay_out_of_dashboard_status(self):
        with patch.object(solar,'_power_guard',solar.MinerPowerGuard()):
            solar.supervise_runtime_by_power(T,'stop',{'collectionTime':T.timestamp(),'dataList':payload()['dataList'][:2]})
            reason=solar._build_snapshot_payload()['power_guard_reason']
            self.assertNotIn('power_fields',reason)
            self.assertNotIn('ESP_VER',reason)


if __name__=='__main__':
    unittest.main()
