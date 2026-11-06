#!/usr/bin/env python3
"""Execute the ten staged pruning gates after terminal incremental success."""

import argparse
import fcntl
import importlib.util
import json
import os
import signal
import subprocess
import time
from pathlib import Path

from audit_completed_batch import sha
from audit_pruning_batch import audit_pruning
from validate_completed_batch import review_pins


def save(path, value):
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def execute(plan_path):
    plan = json.loads(plan_path.read_text())
    assert plan['status'] == 'PREPARED_UNEXECUTED_PRUNING_VALIDATION_NOT_ACCEPTED'
    run, output = Path(plan['run']), plan_path.parent
    state = json.loads((run / 'process.json').read_text())
    status = json.loads((run / 'build/STATUS.json').read_text())
    if state.get('exit_code') != 0 or status.get('status') != 'passed':
        raise ValueError('Pruning build is not terminal and fully passed; validation not started')
    assert not (output / 'report.json').exists(), 'use fresh staged inputs for a new validation attempt'
    assert len(plan['steps']) == len({s['label'] for s in plan['steps']}) == 10
    assert sorted(c['count'] for c in plan['comparisons']) == [1, 33, 183, 696]
    with Path('/tmp/wu-lean-exclusive.lock').open('a') as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        pins = review_pins(plan)
        initial = audit_pruning(run)
        assert initial['lean'] == plan['lean'] and initial['package_paths'] == plan['package_paths']
        save(output / 'context-before.json', initial)
        save(output / 'pin-review.json', pins)
        bindings = {**plan['bindings'], **pins['bindings'], str(plan_path): sha(plan_path)}
        here = Path(__file__).resolve().parent
        checker_path = here.parents[1] / 'scripts/check.py'
        for path in [Path(__file__).resolve(), here / 'audit_pruning_batch.py', here / 'audit_completed_batch.py', here / 'validate_completed_batch.py', checker_path]:
            bindings[str(path)] = sha(path)

        def check_bindings():
            for filename, expected in bindings.items():
                assert sha(Path(filename)) == expected, filename

        spec = importlib.util.spec_from_file_location('pruning_axiom_checker', checker_path)
        checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checker)
        (output / 'tmp').mkdir(exist_ok=True)
        report = dict(status='PRUNING_VALIDATION_RUNNING_NOT_INSTALLED', steps=[], current=None, plan_sha256=sha(plan_path), context_digest=initial['context_digest'], fresh_source_compilations=initial['fresh_source_compilations'], verified_unchanged=initial['verified_unchanged'], bindings=bindings)
        save(output / 'report.json', report)
        handlers = {s: signal.getsignal(s) for s in [signal.SIGINT, signal.SIGTERM]}

        def interrupted(signum, frame):
            raise InterruptedError(f'Pruning validation interrupted by signal {signum}')

        for signum in handlers:
            signal.signal(signum, interrupted)
        try:
            for step in plan['steps']:
                check_bindings()
                label = step['label']
                payload = Path(step['payload']) if step.get('payload') else None
                if payload:
                    assert not payload.exists(), payload
                env = os.environ.copy()
                for key in ['LEAN_PATH', 'LEAN_SYSROOT', 'LEAN_SRC_PATH']:
                    env.pop(key, None)
                env.update(LEAN_PATH=':'.join([step['library'], *plan['package_paths']]), LEAN_SYSROOT=str(Path(plan['lean']).parent.parent), TMPDIR=str(output / 'tmp'))
                log, resources = output / (label + '.log'), output / (label + '.resources')
                command = ['/usr/bin/time', '-v', '-o', str(resources), *step['command']]
                invocation_path = output / (label + '.invocation.json')
                invocation = dict(command=step['command'], execution_command=command, environment={k: env[k] for k in ['LEAN_PATH', 'LEAN_SYSROOT', 'TMPDIR']})
                report['current'] = label
                save(output / 'report.json', report)
                start = time.monotonic()
                with log.open('x') as stream:
                    child = subprocess.Popen(command, cwd=output, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                    invocation['pid'] = child.pid
                    save(invocation_path, invocation)
                    try:
                        rc = child.wait(timeout=step.get('timeout_seconds', 3600))
                    except BaseException:
                        if child.poll() is None:
                            try:
                                os.killpg(child.pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                        invocation['aborted_exit_code'] = child.wait()
                        save(invocation_path, invocation)
                        raise
                row = dict(label=label, exit_code=rc, seconds=time.monotonic() - start, log_sha256=sha(log), resources_sha256=sha(resources), invocation_sha256=sha(invocation_path))
                report['steps'].append(row)
                save(output / 'report.json', report)
                print(label, rc, round(row['seconds'], 2), flush=True)
                assert type(rc) is int and rc == step['expected_exit_code'] == 0, label
                text = log.read_text()
                if label == plan['fresh_kernel_module']:
                    union_object = output / (plan['fresh_kernel_module'] + '.olean')
                    bindings[str(union_object)] = sha(union_object)
                elif label == 'literal-axioms':
                    checker.check_axiom_output(text, {'WuPaper.ClassicalSlots.one8938', 'WuPaper.ClassicalSlots.one894', 'WuPaper.ClassicalSlots.classical_lower', 'WuLiteralAcceptance', 'WuLegacyLiteralAcceptance'})
                elif label == 'after-selberg-type':
                    checker.check_axiom_output(text, {'MathlibNt.SieveTheory.SelbergUpperBound.mainSum_cauchy_schwarz_lower_bound'})
                elif label == 'retirement-after-absent':
                    absence = json.loads(payload.read_text())
                    assert absence['schema'] == 'wu-retired-declaration-absence-v1'
                    assert absence['status'] == 'RAW_PRIVATE_INCLUSIVE_RETIREMENT_ABSENCE_NOT_PROOF_ACCEPTANCE'
                    assert absence['requestedCount'] == absence['absentCount'] == plan['retirement_targets']
                    assert plan['retirement_targets'] >= 6302
                    assert absence['expectedResearchModules'] == plan['retirement_expected_modules'] == 4151
                elif label == 'fresh-kernel-union':
                    assert step['command'] == [str(Path(plan['lean']).with_name('leanchecker')), '--verbose', '--fresh', plan['fresh_kernel_module']]
                    assert text.strip() == 'replaying ' + plan['fresh_kernel_module'] + ' with --fresh'
                    report['fresh_kernel_union_object_sha256'] = sha(output / (plan['fresh_kernel_module'] + '.olean'))
                for pair in plan['comparisons']:
                    if label != pair['label']:
                        continue
                    reference, actual = json.loads(Path(pair['reference']).read_text()), json.loads(payload.read_text())
                    assert reference == actual, label
                    assert len(actual['declarations'] if pair['format'] == 'declarations' else actual) == pair['count'], label
                    row['payload_sha256'] = sha(payload)
                    row['reference_sha256'] = sha(Path(pair['reference']))
                if payload:
                    row['payload_sha256'] = sha(payload)
                    bindings[str(payload)] = sha(payload)
                check_bindings()
                save(output / 'report.json', report)
            assert len(report['steps']) == 10 and 'fresh_kernel_union_object_sha256' in report
            final = audit_pruning(run)
            assert final == initial and review_pins(plan) == pins
            save(output / 'context-after.json', final)
            report.update(status='PRUNING_FULL_CONTEXT_TYPES_VALUES_LITERALS_RETIREMENTS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED', current=None, comparisons=plan['comparisons'], retired_names_absent=plan['retirement_targets'])
            save(output / 'report.json', report)
            print('PRUNING_VALIDATION_PASS_NOT_INSTALLED', str(output), flush=True)
        except BaseException as error:
            report.update(status='PRUNING_VALIDATION_FAILED_NOT_INSTALLED', error_type=type(error).__name__, error=str(error))
            save(output / 'report.json', report)
            raise
        finally:
            for signum, handler in handlers.items():
                signal.signal(signum, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    args = parser.parse_args()
    execute(args.plan.resolve())


if __name__ == '__main__':
    main()
