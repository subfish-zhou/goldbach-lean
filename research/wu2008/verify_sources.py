#!/usr/bin/env python3
"""Check source/history bytes and complete manifest coverage; not a Lean proof."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources=json.loads((root/'source-manifest.json').read_text())
history=json.loads((root/'history-manifest.json').read_text())
expected=set()
for row in sources:
 p=root/'src'/Path(*row['module'].split('.')).with_suffix('.lean')
 assert p.is_file() and not p.is_symlink(),str(p)
 assert sha(p)==row['source_sha256'],str(p)
 expected.add(p)
assert expected==set((root/'src').rglob('*.lean')),'unlisted or missing source'
for row in history:
 h=row['sha256'];p=root/'history'/h[:2]/(h+'.lean')
 assert sha(p)==h,str(p)
print(json.dumps({'source_modules':len(sources),'historical_path_records':len(history),
 'historical_unique_sources':len({r['sha256'] for r in history}),
 'historical_worktrees':len({r['worktree'] for r in history}),
 'source_hash_check':'passed','lean_build':'separate'},indent=2))
