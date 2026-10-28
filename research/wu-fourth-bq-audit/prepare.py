#!/usr/bin/env python3
"""Capture the accepted Eighth baseline for the separate Fourth Bq compression audit."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('checks', ROOT / 'scripts/check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def write(name, value):
    (HERE/name).write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    args = parser.parse_args()
    index = json.loads((args.baseline/'baseline-source-index.json').read_text())
    acceptance = json.loads((args.baseline/'baseline-acceptance.json').read_text())
    require(len(index) == 4431 and sum(v['code_lines'] for v in index.values()) == 601997,
            'Wrong accepted Eighth source baseline')
    require(acceptance['status'] == 'pass' and acceptance['modules'] == 4431,
            'Wrong accepted Eighth build receipt')
    sources = {}
    with tarfile.open(args.baseline/'baseline.tar') as archive:
        for item in archive:
            if not item.isfile() or not item.name.startswith('src/') or not item.name.endswith('.lean'):
                continue
            module = '.'.join(Path(item.name).relative_to('src').with_suffix('').parts)
            require(module not in sources, f'Duplicate archived module: {module}')
            raw = archive.extractfile(item).read()
            require(module in index and hashlib.sha256(raw).hexdigest() == index[module]['sha256'],
                    f'Archive/index mismatch: {module}')
            sources[module] = raw.decode()
    require(set(sources) == set(index), 'Archive and index have different module sets')
    statements = {}
    excluded = []
    for module, text in sources.items():
        if not module.startswith('WR2ClassicalFourth'):
            continue
        if module.startswith('WR2ClassicalFourthBlockLog'):
            excluded.append(module)
            continue
        code = checks.code_only(text, keep_strings=True)
        for found in re.finditer(r'\b(?:theorem|lemma)\s+(\w+)\b(.*?)\s*:=', code, re.S):
            key = module+':'+found[1]
            require(key not in statements, f'Duplicate contract: {key}')
            statements[key] = ''.join(found[2].split())
    # Refuse to silently recapture an already initialized baseline.
    for name in ['baseline-source-index.json', 'baseline-acceptance.json']:
        target = HERE/name
        require(not target.exists() or target.read_bytes() == (args.baseline/name).read_bytes(),
                f'Refusing baseline replacement: {name}')
        shutil.copyfile(args.baseline/name, target)
    write('baseline-statements.json', statements)
    signature = re.search(r'^def Bq\b(.*?)\s*:=', sources['WR2ClassicalFourthDataBq'], re.M | re.S)
    require(signature is not None, 'Missing original Bq declaration')
    write('baseline-declarations.json', {'WR2ClassicalFourthDataBq:Bq': ''.join(signature[1].split())})
    write('preserved-data.json', {'WR2IntegerLogHorner': index['WR2IntegerLogHorner']['sha256'],
                                 'WR2ClassicalCumulativeDivision': index['WR2ClassicalCumulativeDivision']['sha256'],
                                 'WR2IntegerLogUpper': index['WR2IntegerLogUpper']['sha256'],
                                 'WR2ClassicalFourthTableCheck': index['WR2ClassicalFourthTableCheck']['sha256'],
                                 'WR2ExactRationalLog': index['WR2ExactRationalLog']['sha256'],
                                 'WR2ClassicalCertificate': index['WR2ClassicalCertificate']['sha256']})
    write('excluded-log-contract-modules.json', sorted(excluded))
    write('scaffold-status.json', {
        'status': 'prepared_not_accepted', 'baseline': 'accepted Eighth integer compression',
        'baseline_modules': 4431, 'baseline_code_lines': 601997,
        'archive_index_hash_matches': len(sources),
        'retained_non_log_fourth_statements': len(statements),
        'allowed_source_changes': 'DataBq, AllLog, retired BlockLog modules, and new BqSoundness only',
        'shared_horner_must_remain_byte_identical': True,
        'production_fourth_bq_validation': 'pending', 'lean_run_by_this_scaffold': False})
    print(f'PREPARED: {len(sources)} archived hashes verified, {len(statements)} retained Fourth non-Log contracts; no acceptance claimed.')


if __name__ == '__main__':
    main()
