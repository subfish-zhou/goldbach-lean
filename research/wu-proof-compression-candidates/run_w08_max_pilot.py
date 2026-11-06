#!/usr/bin/env python3
"""Compile the isolated max-envelope modules against an unchanged checked base.

This is a local source pilot, not downstream or final theorem acceptance.
"""

import argparse
import fcntl
import json
import os
import shutil
import signal
import subprocess
import time
from pathlib import Path

from audit_completed_batch import EXTENSIONS, audit, sha
from validate_completed_batch import review_pins


def save(path, value):
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--library-base', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    candidate, base, output = args.candidate.resolve(), args.library_base.resolve(), args.output_dir.resolve()
    assert not output.exists()
    record = json.loads((candidate / 'report.json').read_text())
    assert record['status'] == 'UNCOMPILED_W08_MAX_ENVELOPE_DRAFT_NOT_INSTALLED_OR_ACCEPTED'
    assert sha(candidate / 'executed-preparer.py') == record['preparer_sha256']
    plan_path = base.parent / 'validation-inputs-02/validation-plan.json'
    plan = json.loads(plan_path.read_text())
    baseline_report = json.loads((plan_path.parent / 'report.json').read_text())
    assert baseline_report['status'] == 'FULL_CONTEXT_EXPORTS_LITERALS_RETIREMENT_21_KERNELS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED'
    assert len(baseline_report['steps']) == 34 and Path(plan['run']) == base
    bindings = {str(p): sha(p) for p in [Path(__file__).resolve(), candidate / 'report.json', candidate / 'executed-preparer.py', plan_path, plan_path.parent / 'report.json']}
    changed = {r['module']: r for r in record['files']}
    assert len(changed) == 9
    for name, row in changed.items():
        relative = Path(name + '.lean')
        assert sha(base / 'src' / relative) == row['before_sha256'], name
        assert sha(candidate / 'src' / relative) == row['after_sha256'], name
        bindings[str(candidate / 'src' / relative)] = row['after_sha256']
    order, seen = [], set()

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        for dependency in changed[name]['candidate_local_imports']:
            if dependency in changed:
                visit(dependency)
        order.append(name)

    for name in ['W08KernelMatrix', 'W08Envelope', 'W08Entries0', 'W08EntriesRest', 'W08FrozenConsumer', 'W17JointSplit', 'W08Audit', 'W08Root', 'W17ParentFullTypes']:
        visit(name)
    with Path('/tmp/wu-lean-exclusive.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        before = audit(base, Path(plan['baseline']))
        assert before['context_digest'] == baseline_report['context_digest']
        pins = review_pins(plan)
        output.mkdir(parents=True)
        save(output / 'context-before.json', before)
        save(output / 'pins.json', pins)
        for source in (base / 'build/lib').rglob('*'):
            if not source.is_file():
                continue
            relative = source.relative_to(base / 'build/lib')
            if any(str(relative) == str(Path(*n.split('.')).with_suffix(ext)) for n in changed for ext in EXTENSIONS):
                continue
            destination = output / 'lib' / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            os.link(source, destination)
        for name in changed:
            destination = output / 'src' / (name + '.lean')
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(candidate / 'src' / (name + '.lean'), destination)
            destination.chmod(0o444)
        (output / 'tmp').mkdir()
        state = dict(status='LOCAL_W08_SOURCE_PILOT_RUNNING_NOT_ACCEPTED', pid=os.getpid(), start_ticks=Path(f'/proc/{os.getpid()}/stat').read_text().split()[21], started_unix=time.time(), order=order, steps=[], bindings=bindings, library_base=str(base), source_templates_identical_to_validated_base=True)
        save(output / 'process.json', state)
        child = None

        def stop(signum, frame):
            raise InterruptedError(f'W08 pilot interrupted by {signum}')

        handlers = {s: signal.getsignal(s) for s in [signal.SIGINT, signal.SIGTERM]}
        for signum in handlers:
            signal.signal(signum, stop)
        env = os.environ.copy()
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
            env.pop(key, None)
        env.update(LEAN_PATH=':'.join([str(output / 'lib'), *plan['package_paths']]), LEAN_SYSROOT=str(Path(plan['lean']).parent.parent), TMPDIR=str(output / 'tmp'))
        print('LOCAL_W08_PILOT_STARTED', os.getpid(), flush=True)
        try:
            for name in order:
                for p, expected in bindings.items():
                    assert sha(Path(p)) == expected, p
                source, target = output / 'src' / (name + '.lean'), output / 'lib' / (name + '.olean')
                assert sha(source) == changed[name]['after_sha256']
                command = [plan['lean'], '-j1', '-DwarningAsError=true', '-DautoImplicit=false', '-DmaxRecDepth=16384', '-R', str(output / 'src'), '-o', str(target), str(source)]
                log, resources = output / (name + '.log'), output / (name + '.resources')
                measured = ['/usr/bin/time', '-v', '-o', str(resources), *command]
                start = time.monotonic()
                with log.open('x') as handle:
                    child = subprocess.Popen(measured, cwd=output, env=env, stdout=handle, stderr=subprocess.STDOUT, start_new_session=True)
                    invocation = dict(command=command, execution_command=measured, environment={k: env[k] for k in ['LEAN_PATH', 'LEAN_SYSROOT', 'TMPDIR']}, child_pid=child.pid)
                    save(output / (name + '.invocation.json'), invocation)
                    state.update(current=name, child_pid=child.pid)
                    save(output / 'process.json', state)
                    rc = child.wait(timeout=1800)
                row = dict(module=name, exit_code=rc, seconds=time.monotonic() - start, source_sha256=sha(source), log_sha256=sha(log), resources_sha256=sha(resources), invocation_sha256=sha(output / (name + '.invocation.json')))
                if rc == 0:
                    row['artifact_bundle'] = {ext: sha(target.with_suffix(ext)) for ext in EXTENSIONS if target.with_suffix(ext).exists()}
                state['steps'].append(row)
                save(output / 'process.json', state)
                print(name, rc, round(row['seconds'], 2), flush=True)
                assert rc == 0, log.read_text()
            assert audit(base, Path(plan['baseline'])) == before and review_pins(plan) == pins
            state.update(status='LOCAL_NINE_MODULE_SOURCE_COMPILE_PASS_NOT_DOWNSTREAM_OR_KERNEL_ACCEPTANCE', current=None, exit_code=0, finished_unix=time.time())
            save(output / 'result.json', state)
            save(output / 'process.json', state)
            print(state['status'], flush=True)
        except BaseException as error:
            state.update(status='LOCAL_W08_SOURCE_PILOT_STOPPED_NOT_ACCEPTED', error_type=type(error).__name__, error=str(error), finished_unix=time.time())
            save(output / 'process.json', state)
            save(output / 'result.json', state)
            raise
        finally:
            if child is not None and child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            for signum, handler in handlers.items():
                signal.signal(signum, handler)


if __name__ == '__main__':
    main()
