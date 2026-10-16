"""Offline guard replay; recorded controller state is not physical rig status."""
import argparse
from collections import Counter
from datetime import datetime
import json
import math
from pathlib import Path

from miner_power_guard import MinerPowerGuard, PowerSample


def replay(rows, assume_start_commands=False):
    guard = MinerPowerGuard()
    previous_state = None
    previous_at = None
    totals = Counter()
    pulses = []
    for row in rows:
        at = datetime.fromisoformat(row['ts'])
        if previous_at is not None and at <= previous_at:
            totals['repeated_or_out_of_order_rows'] += 1
            continue
        previous_at = at
        values = [float(row[k]) for k in ('inv_lt', 'inv_l1', 'inv_l2', 'inv_l3')]
        # Old telemetry contains inverter outputs, not a separate load meter.
        sample = PowerSample(at, *values) if all(math.isfinite(v) and v >= 0 for v in values) else None
        state = row['state']
        totals['rows'] += 1
        totals['stop_rows_over_1000W'] += state == 'stop' and values[0] > 1000
        if previous_state == 'stop' and state == 'production':
            totals['recorded_start_transitions'] += 1
            if assume_start_commands:
                guard.command_start(sample, at)
                totals['stable_start_baselines'] += guard.started is not None
        before = guard.signature
        if guard.observe(sample, at, state):
            pulses.append({'ts': row['ts'], 'inverter_total_w': values[0]})
        totals['identified_runs'] += before is None and guard.signature is not None
        previous_state = state
    return {
        'counts': dict(totals), 'simulated_shutdown_signals': pulses,
        'assumed_start_commands_from_state_changes': assume_start_commands,
        'limitations': [
            'inv_lt is inverter output, not independently measured consumption.',
            'Controller state is intent, not ground truth for the physical rig.',
            'Without explicit opt-in, no GPIO start commands are inferred.',
            'Old logs omit idle measurements, limiting baseline calibration.',
            'This replay does not measure appliance-classification accuracy.',
        ],
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--telemetry', type=Path, required=True)
    parser.add_argument('--assume-start-commands-from-state-changes', action='store_true',
                        help='Exploratory only: software transitions are not verified GPIO events.')
    args = parser.parse_args()
    print(json.dumps(replay(json.loads(args.telemetry.read_text()),
                            args.assume_start_commands_from_state_changes), indent=2))
