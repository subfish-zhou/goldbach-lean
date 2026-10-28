"""Serial raw-constant census over one completed, verified V7 library.

No adoption, deletion, proof acceptance or automatic queue modification.
Default checks preparation only; execution requires actual corrected gates and terminal workers.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
import signal
import sys
import time

HERE = Path(__file__).resolve().parent
BASE = Path('/tmp/wu-main-port-audit')
ADAPTER = Path('/tmp/wu-structural-full-probe-v7')
STATIC = Path('/tmp/wu-structural-full-validation-v7/validate.py')
VALIDATOR = Path('/tmp/wu-public-census-output-validator/validate.py')
RUN = ADAPTER/'full/run-1793131987644216375'
LEASE = Path('/tmp/wu-lean-exclusive.lock')
POST_PLAN_SHA = 'fe6a9b8660db03f15f75a1f1b955d48b56a1b1bd7d211d99864513c495beffe3'
FULL_PLAN_SHA = '04d9a31438198668bfec595f9949f2e1e32e9aef7dc425f051c99d8419fa1410'
LABELS = ['kernel-checked-endpoint', 'kernel-baseline-original-panel0',
          'kernel-baseline-panel1', 'kernel-baseline-panel39',
          'structural-acceptance-evidence', 'uniform-semantic-trial']


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def verify(bindings):
    for name, digest in bindings.items():
        path = Path(name)
        need(path.is_file() and not path.is_symlink() and sha(path) == digest,
             'input changed or missing: '+name)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def identity(pid):
    try:
        f = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
        return None if f[0] == 'Z' else f[19]
    except (FileNotFoundError, ProcessLookupError):
        return None


PRIOR = HERE/'prior-gates.json'
PRIOR_SHA = '94b1c5db16caa63fe1dae49ef31d95b73353e17bcb5c8ae86fd1b4ada32d8ef0'


def terminal_superseded_post(state):
    """The original failure stays a failure; it is never relabelled successful."""
    need(state.get('plan_sha256') == POST_PLAN_SHA, 'wrong original post plan')
    rows = state.get('completed')
    need(type(rows) is list and len(rows) == 5, 'original failed sequence differs')
    need([r.get('label') for r in rows] == LABELS[:5], 'original gate order differs')
    need(all(type(r.get('exit_code')) is int and r['exit_code'] == 0
             for r in rows[:4]), 'original control kernel gates did not pass')
    need(type(rows[4].get('exit_code')) is int and rows[4]['exit_code'] == 1,
         'original fifth gate failure not preserved')
    need(state.get('status') == 'gate_failed_no_adoption',
         'original failed controller not terminal')


def terminal_corrected(report, marker, dry_run):
    need(report.get('status') == 'PLANNED_GATES_PASSED_NOT_ROOT_ACCEPTANCE_NOT_ADOPTED',
         'corrected complete evidence gate not passed')
    need(report.get('run') == str(RUN) and report.get('plan_sha256') == FULL_PLAN_SHA,
         'corrected evidence run/plan differs')
    for key, value in dict(verified_modules=4151, source_compiled=3500,
                           verified_unchanged=651, actual_types=736, actual_values=183,
                           kernel_replays=65, raw_exact_values=179, bridged_values=4,
                           reused_actual_bridge_kernel_replays=2).items():
        need(type(report.get(key)) is int and report[key] == value,
             'corrected evidence scope differs: '+key)
    need(report.get('value_comparison_mode') == '179_raw_exact_4_bounded_kernel_bridges',
         'corrected value policy differs')
    steps = report.get('steps')
    need(type(steps) is list and len(steps) == 78
         and all(type(row.get('exit_code')) is int and row['exit_code'] == 0
                 for row in steps), 'corrected complete gate steps did not all pass')
    need(marker.get('status') == 'structural_acceptance_passed'
         and marker.get('accepted_by') == 'root'
         and marker.get('run_directory') == str(RUN)
         and marker.get('plan_sha256') == FULL_PLAN_SHA,
         'actual root structural acceptance missing')
    need(dry_run.get('status') == 'DRY_RUN_FULLY_VALIDATED_READY_FOR_REVIEW'
         and dry_run.get('run') == str(RUN) and dry_run.get('production_modified') is False
         and type(dry_run.get('orphaned_receipts')) is int
         and dry_run['orphaned_receipts'] == 4709,
         'actual corrected dry-run missing or different')
    need(type(dry_run.get('required_free_bytes')) is int
         and type(dry_run.get('actual_free_bytes')) is int
         and dry_run['actual_free_bytes'] >= dry_run['required_free_bytes'] > 0,
         'actual dry-run capacity gate not passed')


def controllers_clear():
    need(sha(PRIOR) == PRIOR_SHA, 'corrected prior evidence configuration changed')
    prior = read(PRIOR)
    need(prior['status'] == 'ROOT_REVIEWED_TERMINAL_CORRECTED_GATES_AND_DRY_RUN_NOT_ADOPTION',
         'prior evidence not reviewed')
    verify(prior['bindings'])
    need(sha(BASE/'post-controls-gates-plan.json') == POST_PLAN_SHA,
         'original post-controller plan changed')
    old_plan = read(BASE/'post-controls-gates-plan.json')
    verify(old_plan['bindings'])
    state = read(BASE/'post-controls-gates-watch.json')
    terminal_superseded_post(state)
    report, marker, dry_run = [read(prior[k]) for k in
                               ['corrected_report', 'root_marker', 'dry_run']]
    terminal_corrected(report, marker, dry_run)
    need(marker['validator_report']['path'] == prior['corrected_report']
         and marker['validator_report']['sha256'] == sha(prior['corrected_report']),
         'root accepted a different corrected gate report')
    adopter = load(Path(prior['adopter']), 'census_corrected_adopter_gate')
    adopter.gate_report(report, read(ADAPTER/'full/plan.json'), RUN)
    for process in prior['cleared_processes']:
        pid, ticks = process['pid'], process['start_ticks']
        need(type(pid) is int and pid > 0 and isinstance(ticks, str) and ticks.isdecimal(),
             'missing genuine process identity')
        need(identity(pid) != ticks, 'recorded original/corrected proof worker still live')
    for row in state['completed'] + report['steps']:
        need(sha(row['log']) == row['log_sha256'], 'prior gate log changed')
    need(prior['main_run'] == str(RUN) and prior['main_plan_sha256'] == FULL_PLAN_SHA
         and old_plan['main_run'] == str(RUN)
         and old_plan['main_plan_sha256'] == FULL_PLAN_SHA,
         'prior evidence used a different main run')
    return dict(status='ACTUAL_CORRECTED_GATES_AND_DRY_RUN_VERIFIED_NOT_ADOPTED',
                original_failed_controller=state, corrected_report=prior['corrected_report'],
                corrected_report_sha256=sha(prior['corrected_report']),
                root_marker=prior['root_marker'], root_marker_sha256=sha(prior['root_marker']),
                dry_run=prior['dry_run'], dry_run_sha256=sha(prior['dry_run']))


def relocated_source(original, expected_output, new_output):
    old = json.dumps(expected_output, ensure_ascii=False)
    new = json.dumps(str(new_output), ensure_ascii=False)
    need(original.count(old) == 1, 'expected unique embedded output literal')
    return original.replace(old, new)


def successful_artifacts(row, source, output, obj, log, resources):
    need(type(row.get('exit_code')) is int and row['exit_code'] == 0,
         'metadata file cannot excuse a failed Lean process')
    for name, path in [('source_sha256', source), ('output_sha256', output),
                       ('object_sha256', obj), ('log_sha256', log),
                       ('resources_sha256', resources)]:
        need(path.is_file() and not path.is_symlink() and sha(path) == row.get(name),
             'missing or changed actual runtime artifact: '+name)
    invocation = source.parent/'invocation.json'
    need(invocation.is_file() and not invocation.is_symlink()
         and sha(invocation) == row.get('invocation_sha256'),
         'executed invocation changed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute', action='store_true')
    args = parser.parse_args()
    pinfile = HERE/'pins.json'
    pins = read(pinfile)
    pin_hash = sha(pinfile)
    need(sha(Path(__file__)) == pins['runner_sha256'], 'runner changed')
    def verify_tools():
        need(sha(pinfile) == pin_hash, 'runtime pins changed')
        need(sha(Path(__file__)) == pins['runner_sha256'], 'runner changed')
        verify(pins['bindings'])
    verify_tools()
    need(sha(ADAPTER/'full/plan.json') == FULL_PLAN_SHA, 'full plan changed')
    plan = read(ADAPTER/'full/plan.json')
    sys.path.insert(0, str(ADAPTER))
    sys.path.insert(0, str(STATIC.parent))
    validator = load(VALIDATOR, 'census_payload_validator')
    specs, candidates, input_pins = validator.load_real_specs()
    need(len(specs) == 21 and len(candidates) == 2096, 'wrong census scope')
    if not args.execute:
        print(json.dumps(dict(status='STATIC_RUNTIME_PREPARATION_ONLY_NO_LEAN',
                              probes=len(specs), candidates=len(candidates),
                              inputs=input_pins, execution_queued=False)))
        return
    prior = controllers_clear()
    # Verify every frozen import/input before loading execution helpers.
    verify(plan['frozen_inputs'])
    static = load(STATIC, 'census_full_static')
    adapter = load(ADAPTER/'run.py', 'census_full_adapter')
    owned = load(ADAPTER/'owned_process.py', 'census_owned_process')
    adapter.no_live_lean()
    with LEASE.open('a') as lease:
        fcntl.flock(lease.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        adapter.no_live_lean()
        controllers_clear()
        verify_tools()
        before = static.audit_run(RUN)
        out = HERE/('run-'+str(time.time_ns()))
        out.mkdir()
        (out/'tmp').mkdir()
        save(out/'static-before.json', before)
        save(out/'prior-controller.json', prior)
        report = dict(status='CENSUS_RUNNING_NOT_RETIREMENT_OR_PROOF_ACCEPTANCE',
                      main_run=str(RUN), directory=str(out), steps=[],
                      plan_sha256=FULL_PLAN_SHA, pins_sha256=pin_hash,
                      Lean_executed=False, retirementAccepted=False, proofAccepted=False)
        report_path = out/'report.json'
        tracker = owned.TrackedSubprocess(run=out)
        tracker.on_spawn = lambda process: save(out/'own-process.json', dict(
            pid=process.pid, pgid=process.pid, sid=process.pid, uid=os.getuid(),
            start_ticks=tracker.start_ticks, run=str(out)))
        signals = {s: signal.getsignal(s) for s in (signal.SIGINT, signal.SIGTERM)}
        for sig in signals:
            signal.signal(sig, owned.interrupted)
        env = os.environ.copy()
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
            env.pop(key, None)
        env.update(LEAN_SYSROOT=plan['lean_sysroot'],
                   LEAN_PATH=':'.join([str(RUN/'lib'), *plan['package_paths']]),
                   TMPDIR=str(out/'tmp'))
        prepared = read(validator.PREP)
        outputs, index = [], []
        try:
            save(report_path, report)
            for i, (spec, source_plan) in enumerate(zip(specs, prepared['probes'])):
                verify_tools()
                directory = out/f'{i:02}'
                directory.mkdir()
                source, output = directory/'Probe.lean', directory/'uses.json'
                obj, log = directory/'Probe.olean', directory/'compile.log'
                resources = directory/'resources.txt'
                original = Path(source_plan['source'])
                need(sha(original) == source_plan['source_sha256'], 'prepared source changed')
                source.write_text(relocated_source(original.read_text(),
                                                   source_plan['expected_output'], output))
                source_hash = sha(source)
                need(not output.exists() and not obj.exists(), 'stale output/object')
                cmd = [plan['lean'], '-j1', '-DwarningAsError=true',
                       '-DautoImplicit=false', '-DmaxRecDepth=16384', '-R', str(directory),
                       '-o', str(obj), str(source)]
                measured = ['/usr/bin/time', '-v', '-o', str(resources), *cmd]
                row = dict(import_root=spec.root, command=cmd, measured_command=measured,
                           cwd=str(directory), source=str(source), output=str(output),
                           source_sha256=source_hash, prepared_source_sha256=sha(original),
                           environment={k: env[k] for k in ['LEAN_PATH', 'LEAN_SYSROOT', 'TMPDIR']},
                           assigned_modules=list(spec.assigned))
                report['current_probe'] = i
                save(directory/'invocation.json', row)
                invocation_hash = sha(directory/'invocation.json')
                row['invocation_sha256'] = invocation_hash
                save(report_path, report)
                started = time.monotonic()
                try:
                    with log.open('x') as handle:
                        process = tracker.Popen(measured, cwd=directory, env=env,
                                                stdout=handle, stderr=tracker.STDOUT,
                                                start_new_session=True)
                        report['Lean_executed'] = True
                        row['exit_code'] = process.wait(timeout=3600)
                finally:
                    tracker.cleanup()
                    row['seconds'] = time.monotonic()-started
                    row['log_sha256'] = sha(log) if log.exists() else None
                    row['resources_sha256'] = sha(resources) if resources.exists() else None
                    report['steps'].append(row)
                    save(report_path, report)
                need(row['exit_code'] == 0, 'Lean census probe failed: '+spec.root)
                need(sha(source) == source_hash and sha(directory/'invocation.json') == invocation_hash,
                     'executed source/invocation changed')
                row['output_sha256'], row['object_sha256'] = sha(output), sha(obj)
                row['resources'] = static.parse_resources(resources.read_text())
                successful_artifacts(row, source, output, obj, log, resources)
                payload, digest = validator.read_bound_json(output, row['output_sha256'])
                outputs.append((spec.root, payload))
                index.append(dict(import_root=spec.root, output=str(output), output_sha256=digest))
                save(directory/'result.json', row)
                save(report_path, report)
            summary = validator.validate_payloads(specs, candidates, outputs)
            save(out/'input-index.json', index)
            save(out/'payload-consistency.json', summary)
            validator.load_real_specs()
            verify_tools()
            after = static.audit_run(RUN)
            need(after == before, 'library/source/context changed during census')
            save(out/'static-after.json', after)
            for i, row in enumerate(report['steps']):
                directory = out/f'{i:02}'
                successful_artifacts(row, directory/'Probe.lean', directory/'uses.json',
                                     directory/'Probe.olean', directory/'compile.log',
                                     directory/'resources.txt')
            report.update(status='METADATA_CENSUS_EXECUTED_NOT_API_RETIREMENT_OR_PROOF_ACCEPTANCE',
                          current_probe=None, successful_processes=21, scanned_modules=4151,
                          candidate_count=2096, source_binding_summary=input_pins,
                          static_before_sha256=sha(out/'static-before.json'),
                          static_after_sha256=sha(out/'static-after.json'),
                          payload_consistency_sha256=sha(out/'payload-consistency.json'),
                          input_index_sha256=sha(out/'input-index.json'))
            save(report_path, report)
            print(json.dumps(dict(status=report['status'], report=str(report_path))))
        except BaseException as exc:
            report.update(status='CENSUS_FAILED_NOT_ACCEPTANCE',
                          error_type=type(exc).__name__, error=str(exc))
            save(report_path, report)
            raise
        finally:
            try:
                tracker.cleanup()
            except BaseException as exc:
                report.update(status='CENSUS_FAILED_NOT_ACCEPTANCE',
                              failure_stage='owned_process_cleanup',
                              error_type=type(exc).__name__, error=str(exc))
                save(report_path, report)
                raise
            finally:
                for sig, handler in signals.items():
                    signal.signal(sig, handler)


if __name__ == '__main__':
    main()
