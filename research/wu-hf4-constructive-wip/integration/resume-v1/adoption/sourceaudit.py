from pathlib import Path
import json,hashlib
ROOT=Path('/home/azureuser/goldbach-lean/research/wu2008')
B=Path('/tmp/wu-hf4-installed-v7-resume-v1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rel(n,s):return Path(*n.split('.')).with_suffix(s)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def audit(run, P):
    assert {str(p.relative_to(run / 'sources').with_suffix('')).replace('/', '.') for p in (run / 'sources').rglob('*.lean')} == set(P['order'])
    assert {str(p.relative_to(run / 'lib').with_suffix('')).replace('/', '.') for p in (run / 'lib').rglob('*.olean')} == set(P['order'])
    fresh = json.loads((run / 'results.json').read_text())
    base = json.loads((run / 'verified-base-receipts.json').read_text())
    assert len(fresh) == 389 and len(base) == 3762
    F = {r['module']: r for r in fresh}
    assert set(F) == set(P['affected'])
    assert set(base) == set(P['unchanged'])
    assert set(F) | set(base) == set(P['order'])
    hashes = {}
    contexts = {}
    facts = {}
    for n in P['order']:
        r = F.get(n, base.get(n))
        s = run / 'sources' / rel(n, '.lean')
        o = run / 'lib' / rel(n, '.olean')
        assert sha(s) == P['candidate_sources'][n] == r['source_sha256']
        assert sha(o) == r['object_sha256']
        deps = {d: hashes[d] for d in P['graph'][n]}
        dcs = {d: contexts[d] for d in deps}
        assert r['dependencies'] == deps and r['dependency_contexts'] == dcs
        ctx = digest(dict(source_sha256=r['source_sha256'], object_sha256=r['object_sha256'], dependency_contexts=dcs))
        assert ctx == r['context_sha256']
        assert r['artifact_bundle_sha256'] == {x: sha(run / 'lib' / rel(n, x)) for x in ['.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig'] if (run / 'lib' / rel(n, x)).exists()}
        if n in F:
            assert type(r['exit_code']) is int and r['exit_code'] == 0
            assert sha(Path(r['log'])) == r['log_sha256']
            assert sha(Path(r['resource_log'])) == r['resource_sha256']
            cmd = r['command']
            assert cmd[0] == P['lean'] and '-j1' in cmd and ('-DwarningAsError=true' in cmd)
            origin = r.get('resumed_proof_origin')
            prior = Path(json.loads((B / 'resume-inputs.json').read_text())['prior']) if origin else None
            expected_source = prior / 'sources' / rel(n, '.lean') if origin else s
            expected_obj = prior / 'lib' / rel(n, '.olean') if origin else o
            assert cmd[-1] == str(expected_source) and cmd[cmd.index('-o') + 1] == str(expected_obj)
            assert sha(expected_source) == r['source_sha256']
            if origin:
                assert origin['original_receipt'] == str(prior / 'receipts' / rel(n, '.json')) and origin['original_source'] == str(expected_source) and (origin['original_invocation'] == str(prior / 'logs' / (n + '.invocation.json')))
                original = json.loads(Path(origin['original_receipt']).read_text())
                assert sha(Path(origin['original_receipt'])) == origin['original_receipt_sha256'] and original == {k: v for k, v in r.items() if k != 'resumed_proof_origin'}
                assert sha(Path(origin['original_invocation'])) == origin['original_invocation_sha256']
                assert [x for x in cmd if x.startswith('-DautoImplicit=')] == ([P['policies'][n]] if P['policies'][n] else [])
        else:
            rp = Path(r['receipt_path'])
            assert sha(rp) == r['receipt_sha256']
            orig = json.loads(rp.read_text())
            assert orig['exit_code'] == 0 and sha(ROOT / orig['log']) == orig['log_sha256']
            assert orig['context_sha256'] == ctx
        hashes[n] = r['object_sha256']
        contexts[n] = ctx
        facts[n] = dict(source=r['source_sha256'], object=hashes[n], context=ctx, bundle=r['artifact_bundle_sha256'])
    for n in P['retired']:
        assert not (run / 'lib' / rel(n, '.olean')).exists() and (not (run / 'sources' / rel(n, '.lean')).exists())
    assert sha(ROOT / 'source-manifest.json') == P['baseline_manifest_sha256']
    for n, h in P['production_sources'].items():
        assert sha(ROOT / 'src' / rel(n, '.lean')) == h
    return facts
