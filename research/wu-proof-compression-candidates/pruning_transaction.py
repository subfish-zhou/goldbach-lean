"""Reuse the accepted transaction engine with artifact-preserving rollback.

Only compiled artifact rollback uses links. Sources, receipts and metadata keep
independent copies, so later editing cannot modify the rollback evidence.
"""

import importlib.util
import json
import os
import shutil
from pathlib import Path

from audit_completed_batch import sha


def load_engine(root, allowed):
    path = Path(__file__).resolve().parent.parent / 'wu-hf4-constructive-audit/tools/core.py'
    spec = importlib.util.spec_from_file_location('accepted_pruning_transaction_core', path)
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    core.ROOT = root
    core.ALLOWED = frozenset(allowed)

    def restore(transaction):
        journal = json.loads((transaction / 'journal.json').read_text())
        core.require(journal['phase'] in ['mutating', 'rollback_needed'], 'transaction not recoverable')
        core.require(len({i['target'] for i in journal['items']}) == len(journal['items']), 'duplicate journal targets')
        for item in journal['items']:
            core.valid_target(item['target'])
            if item['old_sha256'] is not None:
                core.require(sha(transaction / 'backup' / item['target']) == item['old_sha256'], 'backup changed ' + item['target'])
        for item in reversed(journal['items']):
            target = core.valid_target(item['target'])
            if item['old_sha256'] is None:
                if target.exists():
                    target.unlink()
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            temporary = target.with_name(target.name + '.pruning-rollback')
            core.require(not temporary.exists(), 'stale rollback temporary')
            backup = transaction / 'backup' / item['target']
            if Path(item['target']).is_relative_to('build/lib'):
                os.link(backup, temporary)
            else:
                shutil.copyfile(backup, temporary)
            os.replace(temporary, target)
        for item in journal['items']:
            target = core.valid_target(item['target'])
            core.require((sha(target) if target.exists() else None) == item['old_sha256'], 'rollback incomplete')
        journal['phase'] = 'rolled_back'
        core.save(transaction / 'journal.json', journal)

    core.restore = restore
    return core, dict(accepted_engine=str(path), accepted_engine_sha256=sha(path), adapter_sha256=sha(Path(__file__)))
