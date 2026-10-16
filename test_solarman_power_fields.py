"""Exercise the inverter-only schema reported by the deployed Pi."""
from dataclasses import replace
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
        self.assertEqual(solar._extract_power_sample(data,T).source,'consumption')

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
        self.assertFalse(guard.observe(reading,reading.at,'stop'))

    def test_field_diagnostics_stay_out_of_dashboard_status(self):
        with patch.object(solar,'_power_guard',solar.MinerPowerGuard()):
            solar.supervise_runtime_by_power(T,'stop',{'collectionTime':T.timestamp(),'dataList':payload()['dataList'][:2]})
            reason=solar._build_snapshot_payload()['power_guard_reason']
            self.assertNotIn('power_fields',reason)
            self.assertNotIn('ESP_VER',reason)


if __name__=='__main__':
    unittest.main()
