#!/usr/bin/env python3
"""Validate a prebuilt complete site and publish static files to gh-pages.

The proof workflow is independent. This command never builds Lean or doc-gen4.
Staging directories and prior gh-pages history are preserved.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from build_docs import ROOT, SOURCE_REPO, modules_in, verify_local_links, verify_site
from build_project_structure import verify_export

FORBIDDEN_PARTS = {'.git', '.github', '.lake', '__pycache__', 'comms'}
STATIC_SUFFIXES = {'.html', '.json', '.js', '.css', '.svg', '.txt', '.md', '.bmp',
                   '.png', '.jpg', '.jpeg', '.gif', '.webp', '.ico', '.woff', '.woff2',
                   '.ttf', '.otf', '.eot', '.map', '.pdf', '.gz', '.webmanifest', '.wasm'}
TEXT_SUFFIXES = {'.html', '.json', '.js', '.css', '.svg', '.txt', '.md', '.bmp'}
PRIVATE_TEXT = re.compile(r'/(?:home|Users|mnt)/[A-Za-z0-9._-]+/|comms/(?:inbox|outbox)|github_pat_[A-Za-z0-9_]{20,}|gh[pousr]_[A-Za-z0-9]{20,}|BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY')
SHA = re.compile(r'[0-9a-f]{40}')


def run(args, *, cwd=None, capture=False) -> str:
    result = subprocess.run(list(map(str, args)), cwd=cwd, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None)
    return result.stdout.strip() if capture else ''


def validate_payload(site, *, expected_modules=None):
    site = Path(site).resolve()
    if (site / 'structure').exists() or (site / 'assets/dependencies/index.html').exists():
        raise ValueError('Retired standalone dependency route in payload')
    for route in ('index.html', 'docs/index.html', 'blueprint/index.html',
                  'assets/dependencies/panel.html', 'report/index.html', '.nojekyll'):
        if not (site / route).is_file():
            raise ValueError(f'Missing publication route: {route}')
    info = json.loads((site / 'build-info.json').read_text())
    api = json.loads((site / 'docs/build-info.json').read_text())
    if info.get('scope') != 'full' or api.get('scope') != 'full':
        raise ValueError('Publication requires a full API inventory')
    modules = api['modules']
    if len(set(modules)) != len(modules) or api['module_count'] != len(modules):
        raise ValueError('Invalid API module inventory')
    if expected_modules is not None and set(modules) != set(expected_modules):
        raise ValueError('API inventory differs from the current project sources')
    for key in ('website_source_revision', 'api_source_revision', 'blueprint_source_revision'):
        if not SHA.fullmatch(info.get(key, '')):
            raise ValueError(f'Missing exact source identity: {key}')
    if info['api_source_revision'] != api['source_revision']:
        raise ValueError('API source identity was relabelled during assembly')
    blueprint = json.loads((site / 'blueprint/build-info.json').read_text())
    if info['blueprint_source_revision'] != blueprint.get('source_revision'):
        raise ValueError('Blueprint source identity mismatch')
    structure = json.loads((site / 'assets/dependencies/build-info.json').read_text())
    if not SHA.fullmatch(structure.get('source_revision', '')):
        raise ValueError('Structure data has no exact source identity')
    if info.get('structure_source_revision') != structure['source_revision']:
        raise ValueError('Structure source identity mismatch')
    verify_export(site / 'assets/dependencies', expected_modules=modules, api=site / 'docs')
    if verify_site(site / 'docs', modules, site_root=site) != api['declaration_count']:
        raise ValueError('API declaration census mismatch')
    verify_local_links(site, find_routes=[site / 'docs/find/index.html'])
    files, total = {}, 0
    for path in sorted(site.rglob('*')):
        relative = path.relative_to(site)
        if path.is_symlink():
            raise ValueError(f'Symlink in static payload: {relative}')
        if any(part in FORBIDDEN_PARTS or (part.startswith('.') and part != '.nojekyll')
               for part in relative.parts):
            raise ValueError(f'Private/build directory in payload: {relative}')
        if not path.is_file():
            continue
        if path.suffix not in STATIC_SUFFIXES and path.name not in {'.nojekyll', 'CNAME', 'LICENSE'}:
            raise ValueError(f'Non-static file in publication payload: {relative}')
        data = path.read_bytes()
        if path.suffix == '.wasm' and not data.startswith(b'\x00asm\x01\x00\x00\x00'):
            raise ValueError(f'Invalid WebAssembly asset: {relative}')
        if len(data) >= 100 * 1024 * 1024:
            raise ValueError(f'File exceeds the Git publication size gate: {relative}')
        total += len(data)
        if path.suffix in TEXT_SUFFIXES:
            text = data.decode('utf-8', errors='replace')
            if PRIVATE_TEXT.search(text):
                raise ValueError(f'Private provenance leaked into payload: {relative}')
        files[str(relative)] = hashlib.sha256(data).hexdigest()
    if total > 1_000_000_000:
        raise ValueError('Static site exceeds the conservative 1 GB Pages size gate')
    return {'website_source_revision': info['website_source_revision'],
            'api_source_revision': info['api_source_revision'],
            'blueprint_source_revision': info['blueprint_source_revision'],
            'structure_source_revision': structure['source_revision'],
            'module_count': len(modules), 'declaration_count': api['declaration_count'],
            'file_count': len(files), 'total_bytes': total, 'files': files}


def publish_tree(site, staging, remote, identity, validation):
    """Fast-forward one generated branch; never rewrite the source branch."""
    site, staging = Path(site).resolve(), Path(staging).resolve()
    if staging.exists():
        raise ValueError('Use a new staging directory; existing material is preserved')
    staging.mkdir(parents=True)
    run(['git', 'init', '-q', staging])
    run(['git', 'config', 'user.name', identity[0]], cwd=staging)
    run(['git', 'config', 'user.email', identity[1]], cwd=staging)
    run(['git', 'remote', 'add', 'origin', remote], cwd=staging)
    old = run(['git', 'ls-remote', 'origin', 'refs/heads/gh-pages'], cwd=staging, capture=True)
    if old:
        run(['git', 'fetch', '--depth=1', 'origin', 'gh-pages'], cwd=staging)
        run(['git', 'checkout', '-b', 'gh-pages', 'FETCH_HEAD'], cwd=staging)
        # Only the prior generated branch in this fresh staging checkout is replaced.
        run(['git', 'rm', '-r', '--ignore-unmatch', '.'], cwd=staging)
    else:
        run(['git', 'checkout', '--orphan', 'gh-pages'], cwd=staging)
    for relative, digest in validation['files'].items():
        source = site / relative
        if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
            raise ValueError(f'Payload changed after validation: {relative}')
        destination = staging / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    run(['git', 'add', '--all'], cwd=staging)
    changed = subprocess.run(['git', 'diff', '--cached', '--quiet'], cwd=staging).returncode
    if changed == 1 or not old:
        run(['git', 'commit', '-m', 'Publish documentation for ' + validation['website_source_revision']], cwd=staging)
    elif changed != 0:
        raise RuntimeError('Cannot inspect the staged publication tree')
    revision = run(['git', 'rev-parse', 'HEAD'], cwd=staging, capture=True)
    run(['git', 'push', 'origin', 'HEAD:refs/heads/gh-pages'], cwd=staging)
    remote_revision = run(['git', 'ls-remote', 'origin', 'refs/heads/gh-pages'], cwd=staging, capture=True).split()[0]
    if revision != remote_revision:
        raise RuntimeError('Remote gh-pages revision differs from the published tree')
    return revision


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--publish', action='store_true', help='Perform Git writes after validation')
    parser.add_argument('--configure-pages', action='store_true', help='Select gh-pages / as the Pages publishing source')
    parser.add_argument('--staging', type=Path, help='New preserved staging directory (required to publish)')
    args = parser.parse_args()
    validation = validate_payload(args.site, expected_modules=modules_in(ROOT))
    print(json.dumps({k: v for k, v in validation.items() if k != 'files'}, indent=2))
    if not args.publish:
        if args.configure_pages:
            parser.error('--configure-pages requires --publish')
        return
    if args.staging is None:
        parser.error('--publish requires a new --staging directory')
    current = run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture=True)
    if current != validation['website_source_revision']:
        raise ValueError('Commit the exact website source before publication')
    if run(['git', 'status', '--porcelain'], cwd=ROOT, capture=True):
        raise ValueError('Commit or isolate all source changes before publication')
    remote = run(['git', 'remote', 'get-url', 'origin'], cwd=ROOT, capture=True)
    if remote not in (SOURCE_REPO, SOURCE_REPO + '.git'):
        raise ValueError('Unexpected destination repository')
    identity = (run(['git', 'show', '-s', '--format=%an', 'HEAD'], cwd=ROOT, capture=True),
                run(['git', 'show', '-s', '--format=%ae', 'HEAD'], cwd=ROOT, capture=True))
    revision = publish_tree(args.site, args.staging, remote, identity, validation)
    result = dict(validation, published_revision=revision, branch='gh-pages')
    if args.configure_pages:
        request = args.staging / '.git/pages-request.json'
        request.write_text(json.dumps({'build_type': 'legacy', 'source': {'branch': 'gh-pages', 'path': '/'}}))
        endpoint = 'repos/subfish-zhou/goldbach-lean/pages'
        run(['gh', 'api', '-X', 'PUT', endpoint, '--input', request], cwd=ROOT)
        settings = json.loads(run(['gh', 'api', endpoint], cwd=ROOT, capture=True))
        if settings.get('build_type') != 'legacy' or settings.get('source') != {'branch': 'gh-pages', 'path': '/'}:
            raise RuntimeError('Pages source configuration did not match the requested branch')
        result['pages_settings'] = settings
    (args.staging / '.git/publication-result.json').write_text(json.dumps(result, indent=2))
    print(f'Published gh-pages {revision}; verify the live build record after Pages deploys.')


if __name__ == '__main__':
    main()
