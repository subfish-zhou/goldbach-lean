"""Synthetic process-status and artifact fixtures; no Lean or subprocess calls."""
from pathlib import Path
import copy
import json
import tempfile
import types
import unittest
from unittest.mock import patch
import run as r


class CorrectedPriorGates(unittest.TestCase):
    def actual(self):
        prior=r.read(r.PRIOR)
        return (r.read(prior['old_post_state']),r.read(prior['corrected_report']),
                r.read(prior['root_marker']),r.read(prior['dry_run']))
    def test_original_failure_remains_failed(self):
        state,_,_,_=self.actual();r.terminal_superseded_post(state)
        self.assertEqual(state['status'],'gate_failed_no_adoption')
    def test_original_cannot_be_relabelled_success(self):
        state,_,_,_=self.actual();state['status']='gate_processes_finished_manual_evidence_review_required_no_adoption'
        with self.assertRaises(RuntimeError):r.terminal_superseded_post(state)
    def test_missing_original_control_rejected(self):
        for i in range(5):
            state,_,_,_=self.actual();state['completed'].pop(i)
            with self.subTest(i=i),self.assertRaises(RuntimeError):r.terminal_superseded_post(state)
    def test_failed_original_kernel_rejected(self):
        for i in range(4):
            state,_,_,_=self.actual();state['completed'][i]['exit_code']=1
            with self.subTest(i=i),self.assertRaises(RuntimeError):r.terminal_superseded_post(state)
    def test_boolean_original_exit_rejected(self):
        state,_,_,_=self.actual();state['completed'][0]['exit_code']=False
        with self.assertRaises(RuntimeError):r.terminal_superseded_post(state)
    def test_actual_corrected_complete_evidence_and_dryrun(self):
        _,report,marker,dry=self.actual();r.terminal_corrected(report,marker,dry)
    def test_corrected_failure_not_waived(self):
        _,report,marker,dry=self.actual();report['status']='VALIDATION_FAILED_NOT_ACCEPTANCE'
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_missing_corrected_kernel_rejected(self):
        _,report,marker,dry=self.actual();report['steps'].pop(12)
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_boolean_corrected_step_exit_rejected(self):
        _,report,marker,dry=self.actual();report['steps'][12]['exit_code']=False
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_missing_type_or_value_or_kernel_scope_rejected(self):
        for key in ['actual_types','actual_values','kernel_replays','raw_exact_values','bridged_values']:
            _,report,marker,dry=self.actual();report[key]-=1
            with self.subTest(key=key),self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_unaccepted_root_marker_rejected(self):
        _,report,marker,dry=self.actual();marker['status']='not_accepted'
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_failed_or_mutating_dryrun_rejected(self):
        _,report,marker,dry=self.actual();dry['production_modified']=True
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_wrong_run_rejected(self):
        _,report,marker,dry=self.actual();report['run']='/wrong'
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_insufficient_capacity_rejected(self):
        _,report,marker,dry=self.actual();dry['actual_free_bytes']=0
        with self.assertRaises(RuntimeError):r.terminal_corrected(report,marker,dry)
    def test_real_terminal_process_identities_clear(self):r.controllers_clear()
    def test_each_genuine_original_or_corrected_live_worker_rejects(self):
        for process in r.read(r.PRIOR)['cleared_processes']:
            with self.subTest(pid=process['pid']),patch.object(r,'identity',side_effect=lambda pid,p=process:p['start_ticks']if pid==p['pid']else None),self.assertRaises(RuntimeError):r.controllers_clear()
    def test_pid_reuse_does_not_mean_original_worker_live(self):
        with patch.object(r,'identity',return_value='different-start-ticks'):r.controllers_clear()


class SourceRelocation(unittest.TestCase):
    def test_exact_single_literal_replacement_preserves_other_bytes(self):
        old = '/tmp/old uses.json'; new = Path('/tmp/fresh/uses.json')
        source = 'prefix\nIO.FS.writeFile '+json.dumps(old)+' payload\nsuffix\n'
        self.assertEqual(r.relocated_source(source, old, new),
                         'prefix\nIO.FS.writeFile '+json.dumps(str(new))+' payload\nsuffix\n')

    def test_missing_literal(self):
        with self.assertRaises(RuntimeError): r.relocated_source('prefix', '/tmp/old', Path('/tmp/new'))

    def test_duplicate_literal(self):
        old = '/tmp/old'
        with self.assertRaises(RuntimeError):
            r.relocated_source(json.dumps(old)+' '+json.dumps(old), old, Path('/tmp/new'))

    def test_unicode_and_quoted_paths(self):
        old = '/tmp/路径"/uses.json'; new = Path('/tmp/新"/uses.json')
        self.assertEqual(r.relocated_source(json.dumps(old, ensure_ascii=False), old, new),
                         json.dumps(str(new), ensure_ascii=False))


class ActualArtifacts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.files = [self.directory/name for name in
                      ['Probe.lean', 'uses.json', 'Probe.olean', 'compile.log', 'resources.txt']]
        self.keys = ['source_sha256', 'output_sha256', 'object_sha256',
                     'log_sha256', 'resources_sha256']
        for i, p in enumerate(self.files): p.write_text('synthetic artifact '+str(i))
        self.invocation = self.directory/'invocation.json'; self.invocation.write_text('{}')
        self.row = dict(exit_code=0, invocation_sha256=r.sha(self.invocation),
                        **{k: r.sha(p) for k, p in zip(self.keys, self.files)})

    def check(self): r.successful_artifacts(self.row, *self.files)

    def test_complete_matching_artifacts(self): self.check()

    def test_valid_output_from_failed_compile_rejected(self):
        self.row['exit_code'] = 1
        with self.assertRaises(RuntimeError): self.check()

    def test_boolean_success_rejected(self):
        self.row['exit_code'] = False
        with self.assertRaises(RuntimeError): self.check()

    def test_each_artifact_mutation_rejected(self):
        for p in self.files:
            before = p.read_bytes(); p.write_text('changed')
            with self.subTest(path=p.name), self.assertRaises(RuntimeError): self.check()
            p.write_bytes(before)

    def test_missing_output_rejected(self):
        self.files[1].unlink()
        with self.assertRaises(RuntimeError): self.check()

    def test_symlink_output_rejected(self):
        old = self.files[1]; target = self.directory/'other'; old.rename(target); old.symlink_to(target)
        with self.assertRaises(RuntimeError): self.check()

    def test_invocation_mutation_rejected(self):
        self.invocation.write_text('{"changed":true}')
        with self.assertRaises(RuntimeError): self.check()

    def test_tool_input_mutation_rejected(self):
        p = self.files[0]; bindings = {str(p): r.sha(p)}; r.verify(bindings)
        p.write_text('changed')
        with self.assertRaises(RuntimeError): r.verify(bindings)


class SerialOrchestration(unittest.TestCase):
    """No real Lean metadata, source import, compiler or process is used."""
    def exercise(self, fail_at=None, cleanup_failure=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); adapter = root/'adapter'; (adapter/'full').mkdir(parents=True)
            plan = dict(frozen_inputs={}, lean='/synthetic/lean',
                        lean_sysroot='/synthetic/sysroot', package_paths=['/synthetic/packages'])
            planfile = adapter/'full/plan.json'; planfile.write_text(json.dumps(plan))
            pins = dict(runner_sha256=r.sha(Path(r.__file__)), bindings={})
            (root/'pins.json').write_text(json.dumps(pins))
            probes = []
            for i in range(21):
                p = root/f'prepared-{i}.lean'; old = str(root/f'never-used-{i}.json')
                p.write_text('SYNTHETIC SOURCE ONLY '+json.dumps(old))
                probes.append(dict(source=str(p), source_sha256=r.sha(p), expected_output=old))
            prep = root/'prepared.json'; prep.write_text(json.dumps(dict(probes=probes)))
            specs = [types.SimpleNamespace(root=f'Synthetic{i}', assigned=(f'Module{i}',))
                     for i in range(21)]
            trace = dict(calls=0, active=False, cleanup=0, audits=0)
            def audit(_):
                self.assertFalse(trace['active']); trace['audits'] += 1
                return dict(status='SYNTHETIC_STATIC_AUDIT_ONLY')
            def payloads(actual_specs, candidates, outputs):
                self.assertEqual(len(actual_specs), 21); self.assertEqual(len(outputs), 21)
                self.assertEqual([x[0] for x in outputs], [s.root for s in specs])
                return dict(status='SYNTHETIC_PAYLOAD_TEST_ONLY')
            validator = types.SimpleNamespace(
                load_real_specs=lambda: (specs, list(range(2096)), dict(synthetic=True)),
                PREP=prep, validate_payloads=payloads,
                read_bound_json=lambda p, h: (r.read(p), h))
            static = types.SimpleNamespace(audit_run=audit,
                                           parse_resources=lambda _: dict(synthetic=True))
            test = self
            class Tracker:
                STDOUT = -2
                def __init__(self, run):
                    self.run = run; self.start_ticks = 'SYNTHETIC'; self.on_spawn = lambda p: None
                def Popen(self, command, **kwargs):
                    test.assertFalse(trace['active']); trace['active'] = True
                    n = trace['calls']; trace['calls'] += 1
                    test.assertTrue(kwargs['start_new_session'])
                    test.assertEqual(kwargs['stderr'], self.STDOUT)
                    test.assertEqual(kwargs['env']['LEAN_SYSROOT'], '/synthetic/sysroot')
                    test.assertEqual(kwargs['env']['LEAN_PATH'], str(adapter/'full/run-fixture/lib')+
                                     ':/synthetic/packages')
                    test.assertEqual(command[:2], ['/usr/bin/time', '-v'])
                    test.assertIn('-DwarningAsError=true', command)
                    test.assertIn('-DautoImplicit=false', command)
                    directory = Path(kwargs['cwd'])
                    test.assertFalse((directory/'uses.json').exists())
                    def wait(timeout):
                        test.assertEqual(timeout, 3600)
                        (directory/'uses.json').write_text('{"SYNTHETIC":true}')
                        (directory/'Probe.olean').write_text('SYNTHETIC OBJECT, NOT LEAN')
                        (directory/'resources.txt').write_text('SYNTHETIC RESOURCES')
                        kwargs['stdout'].write('SYNTHETIC LOG, NO PROOF PROCESS\n')
                        trace['active'] = False
                        return 1 if fail_at == n else 0
                    process = types.SimpleNamespace(pid=987654, wait=wait)
                    self.on_spawn(process)
                    return process
                def cleanup(self):
                    trace['active'] = False; trace['cleanup'] += 1
                    if cleanup_failure and trace['calls'] == 21 and trace['audits'] == 2:
                        raise RuntimeError('SYNTHETIC CLEANUP FAILURE')
            owned = types.SimpleNamespace(TrackedSubprocess=Tracker, interrupted=lambda *_: None)
            def loader(path, name):
                return (validator if Path(path) == r.VALIDATOR else static if Path(path) == r.STATIC
                        else owned if Path(path).name == 'owned_process.py'
                        else types.SimpleNamespace(no_live_lean=lambda: test.assertFalse(trace['active'])))
            with patch.object(r, 'HERE', root), patch.object(r, 'ADAPTER', adapter), \
                 patch.object(r, 'LEASE', root/'synthetic-worker.lock'), \
                 patch.object(r, 'RUN', adapter/'full/run-fixture'), \
                 patch.object(r, 'FULL_PLAN_SHA', r.sha(planfile)), \
                 patch.object(r, 'load', side_effect=loader), \
                 patch.object(r, 'controllers_clear', return_value=dict(synthetic=True)), \
                 patch.object(r.signal, 'signal'), patch.object(r.sys, 'argv', ['fixture', '--execute']), \
                 patch('builtins.print'):
                if fail_at is not None or cleanup_failure:
                    with self.assertRaises(RuntimeError): r.main()
                else:
                    r.main()
            runs = list(root.glob('run-*')); self.assertEqual(len(runs), 1)
            report = r.read(runs[0]/'report.json')
            self.assertFalse(trace['active'])
            self.assertFalse(report['retirementAccepted']); self.assertFalse(report['proofAccepted'])
            return trace, report

    def test_all21_runs_serially_in_fresh_directories(self):
        trace, report = self.exercise()
        self.assertEqual(trace['calls'], 21); self.assertEqual(trace['audits'], 2)
        self.assertEqual(report['successful_processes'], 21)
        self.assertEqual(report['status'],
                         'METADATA_CENSUS_EXECUTED_NOT_API_RETIREMENT_OR_PROOF_ACCEPTANCE')

    def test_output_written_by_fourth_failed_probe_does_not_start_fifth(self):
        trace, report = self.exercise(fail_at=3)
        self.assertEqual(trace['calls'], 4); self.assertEqual(trace['audits'], 1)
        self.assertEqual(len(report['steps']), 4)
        self.assertEqual(report['status'], 'CENSUS_FAILED_NOT_ACCEPTANCE')

    def test_final_owned_cleanup_failure_cannot_leave_success_status(self):
        trace, report = self.exercise(cleanup_failure=True)
        self.assertEqual(trace['calls'], 21)
        self.assertEqual(report['status'], 'CENSUS_FAILED_NOT_ACCEPTANCE')
        self.assertEqual(report['failure_stage'], 'owned_process_cleanup')


if __name__ == '__main__':
    unittest.main()
