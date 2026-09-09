#!/usr/bin/env python3
"""Read-only, source-pinned candidate discovery. Hash matches are not proofs."""
from __future__ import annotations
import argparse
from contextlib import closing
import heapq
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess

SCHEMA = 1


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(root: Path, *args: str) -> bytes:
    env = os.environ.copy()
    for key in tuple(env):
        if key in ('GIT_DIR', 'GIT_WORK_TREE') or key.endswith(('_LEDGER_GIT_DIR', '_LEDGER_WORK_TREE')):
            env.pop(key, None)
    return subprocess.check_output(['git', '-C', str(root), *args], env=env)


def utf16_prefix(line: str, column: int) -> str:
    """Lean .ilean declaration positions use zero-based LSP UTF-16 positions."""
    if column < 0:
        raise ValueError('negative column')
    data = line.encode('utf-16-le')
    if 2 * column > len(data):
        raise ValueError('column outside line')
    return data[:2 * column].decode('utf-16-le')


class SourceText:
    def __init__(self, text: str):
        self.text = text
        self.lines = text.split('\n')
        self.offsets = []
        offset = 0
        for line in self.lines:
            self.offsets.append(offset)
            offset += len(line) + 1

    def position(self, line: int, column: int) -> int:
        if line < 0 or line >= len(self.lines):
            raise ValueError('range outside source')
        body = self.lines[line]
        if body.endswith('\r'):
            body = body[:-1]
        return self.offsets[line] + len(utf16_prefix(body, column))

    def slice(self, span: list[int]) -> str:
        if len(span) != 8 or any(type(x) is not int for x in span):
            raise ValueError('unsupported declaration-range schema')
        start, end, name_start, name_end = (self.position(*span[i:i+2]) for i in (0,2,4,6))
        if not start <= name_start <= name_end <= end:
            raise ValueError('inverted range or selection outside declaration')
        return self.text[start:end]


def source_slice(text: str, span: list[int]) -> str:
    return SourceText(text).slice(span)


def file_digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def object_parts(obj: Path) -> dict[str, str]:
    return {str(p): file_digest(p) for p in (obj, Path(str(obj)+'.server'), Path(str(obj)+'.private')) if p.is_file()}


def manifest_key(manifest: dict) -> str:
    return digest(json.dumps(manifest, sort_keys=True, separators=(',', ':')).encode())


def seal_records(manifest: dict, raw: bytes, requested: list[str], extractor_hash: str) -> bytes:
    """Called by runner only after a successful extractor exit and input revalidation.

    Not an authentication boundary: receipts protect against interrupted/mixed runs,
    not an attacker who can replace both payload and receipt.
    """
    counts = {m: 0 for m in requested}
    for line in raw.splitlines():
        row = json.loads(line)
        counts[row['module']] += 1
    if raw and not raw.endswith(b'\n'):
        raw += b'\n'
    receipt = {'record_kind': 'extraction_complete', 'schema': 1,
               'manifest_sha256': manifest_key(manifest), 'extractor_sha256': extractor_hash,
               'records_sha256': digest(raw), 'counts': counts, 'exit_code': 0}
    return raw + json.dumps(receipt, sort_keys=True).encode() + b'\n'


def source_inventory(source: Path, objects: Path) -> dict:
    revision = git(source, 'rev-parse', 'HEAD').decode().strip()
    modules, missing = [], []
    tree = git(source, 'ls-tree', '-rz', '--full-tree', 'HEAD')
    for entry in tree.split(b'\0'):
        if not entry:
            continue
        meta, rel = entry.split(b'\t', 1)
        path = rel.decode()
        if not path.endswith('.lean'):
            continue
        expected = meta.split()[2].decode()
        raw = (source / path).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if actual != expected:
            raise ValueError(f'source differs from HEAD: {path}')
        module = path[:-5].replace('/', '.')
        obj = objects / (path[:-5] + '.olean')
        ilean = objects / (path[:-5] + '.ilean')
        if not obj.is_file() or not ilean.is_file():
            missing.append({'module': module, 'source': path})
            continue
        raw_index = ilean.read_bytes()
        index = json.loads(raw_index)
        if index['module'] != module:
            raise ValueError(f'ilean module mismatch: {path}')
        # Validate all ranges against the pinned source, including supplementary Unicode.
        source_text = SourceText(raw.decode('utf-8'))
        for span in index['decls'].values():
            source_text.slice(span)
        modules.append({'module': module, 'source': path, 'source_sha256': digest(raw),
                        'source_git_blob': expected, 'object': str(obj),
                        'object_parts_sha256': object_parts(obj), 'object_size': obj.stat().st_size, 'object_mtime_ns': obj.stat().st_mtime_ns,
                        'ilean': str(ilean), 'ilean_sha256': digest(raw_index),
                        'decls': index['decls'], 'direct_imports': index['directImports']})
    return {'schema': SCHEMA, 'revision': revision, 'source_root': str(source.resolve()),
            'object_root': str(objects.resolve()), 'modules': modules, 'missing': missing,
            'object_freshness': 'baseline cache; source/range matching is not a fresh compile'}


def validate_manifest(m: dict) -> None:
    if m['schema'] != SCHEMA:
        raise ValueError('unsupported manifest schema')
    root = Path(m['source_root'])
    for item in m['modules']:
        if digest((root / item['source']).read_bytes()) != item['source_sha256']:
            raise ValueError('stale source: ' + item['source'])
        if digest(Path(item['ilean']).read_bytes()) != item['ilean_sha256']:
            raise ValueError('stale ilean: ' + item['module'])
        if object_parts(Path(item['object'])) != item['object_parts_sha256']:
            raise ValueError('object changed (bytes): ' + item['module'])
        stat = Path(item['object']).stat()
        if (stat.st_size, stat.st_mtime_ns) != (item['object_size'], item['object_mtime_ns']):
            raise ValueError('object changed: ' + item['module'])


def build_index(manifest: dict, streams: list[Path], output: Path) -> dict:
    validate_manifest(manifest)
    if output.exists():
        raise FileExistsError(output)
    modules = {m['module']: m for m in manifest['modules']}
    root = Path(manifest['source_root'])
    with closing(sqlite3.connect(output)) as conn:
        conn.executescript('''
          CREATE TABLE metadata(key TEXT PRIMARY KEY, value TEXT NOT NULL);
          CREATE TABLE modules(module TEXT PRIMARY KEY, source TEXT, metadata TEXT);
          CREATE TABLE declarations(name TEXT PRIMARY KEY, module TEXT, kind TEXT,
            explicit INTEGER, source_lines INTEGER, span TEXT, source_hash TEXT,
            type_hash TEXT, shape_hash TEXT, conclusion_head TEXT,
            level_params TEXT, proof_hash TEXT, proof_nodes TEXT, payload TEXT);
          CREATE TABLE ambiguous_declarations(name TEXT PRIMARY KEY);
          CREATE TABLE occurrences(name TEXT, module TEXT, payload TEXT, PRIMARY KEY(name,module));
          CREATE TABLE dependencies(consumer TEXT, provider TEXT, role TEXT,
            PRIMARY KEY(consumer,provider,role));
          CREATE INDEX by_type ON declarations(type_hash,level_params);
          CREATE INDEX by_shape ON declarations(shape_hash);
          CREATE INDEX by_head ON declarations(conclusion_head);
          CREATE INDEX by_provider ON dependencies(provider);
        ''')
        conn.execute('INSERT INTO metadata VALUES (?,?)', ('manifest', json.dumps(manifest)))
        conn.execute('INSERT INTO metadata VALUES (?,?)', ('state', 'building'))
        conn.commit()
        for module, data in modules.items():
            conn.execute('INSERT INTO modules VALUES (?,?,?)', (module, data['source'], json.dumps(data)))
        count = 0
        seen_modules = set()
        texts = {}
        for stream in streams:
            raw = stream.read_bytes()
            lines = raw.splitlines(keepends=True)
            if not lines:
                raise ValueError('missing sealed extraction footer')
            receipt = json.loads(lines[-1])
            payload = b''.join(lines[:-1])
            if (receipt.get('record_kind') != 'extraction_complete' or
                receipt.get('manifest_sha256') != manifest_key(manifest) or
                receipt.get('records_sha256') != digest(payload) or receipt.get('exit_code') != 0):
                raise ValueError('invalid sealed extraction receipt')
            requested = receipt['counts']
            if set(requested) - set(modules) or seen_modules.intersection(requested):
                raise ValueError('unknown module or overlapping sealed modules')
            observed = dict.fromkeys(requested, 0)
            for number, line in enumerate(lines[:-1], 1):
                if not line.strip():
                    continue
                row = json.loads(line)
                module = row['module']
                if module not in modules:
                    raise ValueError(f'unknown module at {stream}:{number}: {module}')
                if module not in observed:
                    raise ValueError('unrequested module in sealed payload')
                observed[module] += 1
                data = modules[module]
                name = row['name']
                span = data['decls'].get(name)
                snippet = ''
                if span:
                    if module not in texts:
                        texts[module] = SourceText((root / data['source']).read_bytes().decode('utf-8'))
                    snippet = texts[module].slice(span)
                # Explicit-source membership is decided by compiler source ranges, not name heuristics.
                values = (name, module, row['kind'], int(span is not None),
                          len(snippet.splitlines()), json.dumps(span), digest(snippet.encode()) if span else None,
                          str(row['type_hash']), str(row['type_shape_hash']), row['conclusion_head'],
                          json.dumps(row['level_params']), None if row['proof_hash'] is None else str(row['proof_hash']),
                          None if row['proof_nodes'] is None else str(row['proof_nodes']), json.dumps(row, sort_keys=True))
                prior = conn.execute('SELECT payload FROM declarations WHERE name=?', (name,)).fetchone()
                occurrence = conn.execute('SELECT payload FROM occurrences WHERE name=? AND module=?', (name,row['module'])).fetchone()
                if occurrence:
                    if occurrence[0] != values[-1]:
                        raise ValueError('conflicting repeated declaration: ' + name)
                    continue
                conn.execute('INSERT INTO occurrences VALUES (?,?,?)', (name,row['module'],values[-1]))
                if prior:
                    # Keep distinct ModuleData occurrences and union their dependencies.
                    # Fingerprints do NOT establish expression equality: ambiguous names
                    # are excluded as targets/providers until independently disambiguated.
                    conn.execute('INSERT OR IGNORE INTO ambiguous_declarations VALUES (?)',(name,))
                else:
                    conn.execute('INSERT INTO declarations VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)', values)
                    count += 1
                for role, field in [('proof', 'direct_deps'), ('type', 'type_deps')]:
                    for dep in row[field]:
                        conn.execute('INSERT OR IGNORE INTO dependencies VALUES (?,?,?)', (name, dep, role))
            if observed != requested:
                raise ValueError('sealed module count mismatch')
            seen_modules.update(requested)
        if count == 0:
            raise ValueError('empty extraction is not an index')
        validate_manifest(manifest)
        summary = {'declarations': count, 'extracted_modules': sorted(seen_modules),
                   'unextracted_modules': sorted(set(modules) - seen_modules), 'verified_replacements': 0,
                   'ambiguous_names_excluded': conn.execute('SELECT count(*) FROM ambiguous_declarations').fetchone()[0]}
        conn.execute('INSERT INTO metadata VALUES (?,?)', ('summary', json.dumps(summary)))
        conn.execute("UPDATE metadata SET value='complete' WHERE key='state'")
        conn.commit()
        return summary


def reachable(graph: dict[str, set[str]], start: str, target: str) -> bool:
    todo, seen = [start], set()
    while todo:
        node = todo.pop()
        if node == target:
            return True
        if node in seen:
            continue
        seen.add(node)
        todo.extend(graph.get(node, ()))
    return False


def candidates(db: Path, limit: int = 100, min_lines: int = 8) -> dict:
    if limit <= 0 or min_lines < 0:
        raise ValueError('positive limit and nonnegative min-lines required')
    with closing(sqlite3.connect(db.resolve().as_uri() + '?mode=ro', uri=True)) as conn:
        conn.row_factory = sqlite3.Row
        state = conn.execute("SELECT value FROM metadata WHERE key='state'").fetchone()
        if state is None or state[0] != 'complete':
            raise ValueError('incomplete index')
        manifest = json.loads(conn.execute("SELECT value FROM metadata WHERE key='manifest'").fetchone()[0])
        summary = json.loads(conn.execute("SELECT value FROM metadata WHERE key='summary'").fetchone()[0])
        validate_manifest(manifest)
        rows = list(conn.execute("SELECT name,module,source_lines,type_hash,shape_hash,conclusion_head,level_params "
                                 "FROM declarations WHERE explicit=1 AND kind IN ('theorem','thm') "
                                 "AND name NOT IN (SELECT name FROM ambiguous_declarations) ORDER BY name"))
        all_names = {x[0] for x in conn.execute('SELECT name FROM declarations')}
        graph = {}
        for a, b in conn.execute('SELECT consumer,provider FROM dependencies'):
            graph.setdefault(a, set()).add(b)
        import_graph = {}
        for m in manifest['modules']:
            imports = m['direct_imports']
            import_graph[m['module']] = {x if isinstance(x, str) else x[0] for x in imports}
        known_project = {n for m in manifest['modules'] for n in m['decls']}
        roots = {m['module'].split('.')[0] for m in manifest['modules']}
        def project_name(name):
            raw = name.removeprefix('_private.')
            return name in known_project or raw.split('.')[0] in roots
        from functools import lru_cache
        @lru_cache(maxsize=256)
        def closure(start):
            todo, seen = [start], set()
            while todo:
                n = todo.pop()
                if n in seen:
                    continue
                seen.add(n)
                todo.extend(graph.get(n, ()))
            return seen
        exact, shapes = {}, {}
        for r in rows:
            exact.setdefault((r['conclusion_head'],r['type_hash'],r['level_params']), []).append(r)
            shapes.setdefault((r['conclusion_head'],r['shape_hash']), []).append(r)
        found, count, unresolved = [], 0, 0
        for a in rows:
            if a['source_lines'] < min_lines or not a['conclusion_head'] or a['name'].startswith('_private.'):
                continue
            matches = {b['name']:b for b in exact[(a['conclusion_head'],a['type_hash'],a['level_params'])]}
            matches.update({b['name']:b for b in shapes[(a['conclusion_head'],a['shape_hash'])]})
            for b in sorted(matches.values(), key=lambda r:r['name']):
                if a['name'] == b['name'] or b['name'].startswith('_private.'):
                    continue
                deps = closure(b['name'])
                if a['name'] in deps:
                    continue
                if any(n not in all_names and project_name(n) for n in deps):
                    unresolved += 1
                    continue
                same_type = a['type_hash'] == b['type_hash'] and a['level_params'] == b['level_params']
                already_imported = a['module'] == b['module'] or reachable(import_graph, a['module'], b['module'])
                if not already_imported and reachable(import_graph, b['module'], a['module']):
                    continue
                count += 1
                record = {'target': a['name'], 'provider': b['name'], 'target_module': a['module'],
                          'provider_module': b['module'], 'target_lines': a['source_lines'],
                          'match': 'type-fingerprint' if same_type else 'shape-fingerprint',
                          'provider_already_imported': already_imported,
                          'status': 'unverified; hash/shape matches require full Lean coverage and dependency checks',
                          'priority': (2 if same_type else 1) * a['source_lines']}
                item = (record['priority'], already_imported, -count, record)
                if len(found) < limit:
                    heapq.heappush(found, item)
                elif item[:3] > found[0][:3]:
                    heapq.heapreplace(found, item)
        return {'revision': manifest['revision'], 'candidate_count': count,
                'candidates': [x[3] for x in sorted(found, reverse=True)],
                'unextracted_modules': summary['unextracted_modules'],
                'rejected_unresolved_project_dependencies': unresolved,
                'dependency_filter_scope': 'indexed graph; external-library closure rechecked by Lean before replacement',
                'scope': 'exact and structural fingerprints among indexed explicit project theorems; not all specializations'}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    s = p.add_subparsers(dest='cmd', required=True)
    m = s.add_parser('manifest'); m.add_argument('--source', type=Path, required=True); m.add_argument('--objects', type=Path, required=True); m.add_argument('--output', type=Path, required=True)
    i = s.add_parser('index'); i.add_argument('--manifest', type=Path, required=True); i.add_argument('--input', type=Path, nargs='+', required=True); i.add_argument('--output', type=Path, required=True)
    c = s.add_parser('candidates'); c.add_argument('--database', type=Path, required=True); c.add_argument('--limit', type=int, default=100); c.add_argument('--min-lines', type=int, default=8); c.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.cmd == 'manifest':
        result = source_inventory(a.source, a.objects)
    elif a.cmd == 'index':
        print(json.dumps(build_index(json.loads(a.manifest.read_text()), a.input, a.output))); return
    else:
        result = candidates(a.database, a.limit, a.min_lines)
    with a.output.open('x') as f:
        json.dump(result, f, indent=2); f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('modules','candidates')} if a.cmd != 'manifest' else {'modules':len(result['modules']),'missing':result['missing'],'revision':result['revision']}))


if __name__ == '__main__':
    main()
