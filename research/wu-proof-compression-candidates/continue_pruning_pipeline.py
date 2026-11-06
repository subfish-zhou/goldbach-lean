#!/usr/bin/env python3
"""Observe the existing pruning build, then run validation without restarting it."""

import argparse
import fcntl
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

from audit_completed_batch import sha
from continue_batch_pipeline import observe_build


def save(path, value):
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--state-dir', type=Path, required=True)
    args = parser.parse_args()
    plan_path, state_dir = args.plan.resolve(), args.state_dir.resolve()
    plan = json.loads(plan_path.read_text())
    assert plan['status'] == 'PREPARED_UNEXECUTED_PRUNING_VALIDATION_NOT_ACCEPTED'
    assert not state_dir.exists()
    run = Path(plan['run'])
    assert not (plan_path.parent / 'report.json').exists()
    state_dir.mkdir(parents=True)
    with (run / 'validation-pipeline.lock').open('a') as queue:
        fcntl.flock(queue, fcntl.LOCK_EX | fcntl.LOCK_NB)
        state_path = state_dir / 'process.json'
        state = dict(status='WAITING_EXISTING_PRUNING_BUILD_NOT_INSTALLED', pid=os.getpid(), start_ticks=Path(f'/proc/{os.getpid()}/stat').read_text().split()[21], started_unix=time.time(), run=str(run), plan=str(plan_path), plan_sha256=sha(plan_path), pipeline_sha256=sha(Path(__file__)), child=None)
        save(state_path, state)
        child = None

        def stop(signum, frame):
            raise InterruptedError(f'Pruning pipeline interrupted by {signum}')

        handlers = {s: signal.getsignal(s) for s in [signal.SIGINT, signal.SIGTERM]}
        for signum in handlers:
            signal.signal(signum, stop)
        print('WAITING_EXISTING_PRUNING_BUILD', run, flush=True)
        try:
            missing_since = None
            while True:
                observation = observe_build(run)
                if observation is None:
                    state['observation_retry_unix'] = time.time()
                    save(state_path, state)
                    time.sleep(10)
                    continue
                build, status = observation
                if 'exit_code' in build:
                    assert build['exit_code'] == 0 and status['status'] == 'passed', 'Existing build terminated without full success'
                    break
                try:
                    live = Path(f"/proc/{build['pid']}/stat").read_text().split()[21] == build['start_ticks']
                except FileNotFoundError:
                    live = False
                if live:
                    missing_since = None
                elif missing_since is None:
                    missing_since = time.monotonic()
                elif time.monotonic() - missing_since > 30:
                    raise RuntimeError('Build handle missing without terminal result; no restart attempted')
                state['last_observation'] = dict(unix=time.time(), build_pid=build['pid'], build_identity_live=live, verified_modules=status.get('verified'), planned_modules=status.get('planned'))
                save(state_path, state)
                time.sleep(10)
            assert sha(plan_path) == state['plan_sha256']
            for path, expected in plan['bindings'].items():
                assert sha(Path(path)) == expected, path
            command = [sys.executable, str(Path(__file__).with_name('validate_pruning_batch.py')), '--plan', str(plan_path)]
            log = state_dir / 'validation.log'
            with log.open('x') as handle:
                child = subprocess.Popen(command, stdout=handle, stderr=subprocess.STDOUT, start_new_session=True)
                state.update(status='PRUNING_VALIDATION_RUNNING_NOT_INSTALLED', child=dict(pid=child.pid, command=command, log=str(log)))
                save(state_path, state)
                rc = child.wait()
            state['child'].update(exit_code=rc, log_sha256=sha(log))
            save(state_path, state)
            assert rc == 0, f'Validation exited {rc}'
            report = json.loads((plan_path.parent / 'report.json').read_text())
            assert report['status'] == 'PRUNING_FULL_CONTEXT_TYPES_VALUES_LITERALS_RETIREMENTS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED'
            assert len(report['steps']) == 10
            state.update(status='PRUNING_BUILD_AND_VALIDATION_PASS_NOT_INSTALLED', finished_unix=time.time(), report_sha256=sha(plan_path.parent / 'report.json'))
            save(state_path, state)
            print(state['status'], flush=True)
        except BaseException as error:
            state.update(status='PRUNING_PIPELINE_STOPPED_NOT_INSTALLED', error_type=type(error).__name__, error=str(error), finished_unix=time.time())
            save(state_path, state)
            raise
        finally:
            # Only this pipeline's validation process is owned here. Never
            # signal the source build being observed.
            if child is not None and child.poll() is None:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
            for signum, handler in handlers.items():
                signal.signal(signum, handler)


if __name__ == '__main__':
    main()
