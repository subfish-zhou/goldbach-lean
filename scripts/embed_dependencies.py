"""Attach optional dependency panels to existing mathematical and API pages."""
from collections import defaultdict
from html import escape
from html.parser import HTMLParser
import json
from pathlib import Path
import posixpath
import re
import shutil
from urllib.parse import urlencode, urlsplit, unquote

VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link',
        'meta', 'param', 'source', 'track', 'wbr'}


class PanelPositions(HTMLParser):
    """Find complete block boundaries, without rewriting the generator's HTML."""
    def __init__(self, text, bindings):
        super().__init__(convert_charrefs=True)
        self.text = text
        self.offsets = [0] + [match.end() for match in re.finditer('\n', text)]
        self.bindings = bindings
        self.stack = []
        self.inserts = []

    def absolute_position(self):
        line, column = self.getpos()
        return self.offsets[line - 1] + column

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        key = attrs.get('data-proof-node')
        if key is not None and key not in self.bindings:
            raise ValueError('Unknown mathematical dependency target: ' + key)
        if key is None and tag in {'div', 'section', 'article'}:
            key = attrs.get('id')
        if tag not in VOID:
            self.stack.append((tag, self.bindings.get(key)))

    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, -1, -1):
            if self.stack[i][0] == tag:
                binding = self.stack[i][1]
                del self.stack[i:]
                if binding:
                    self.inserts.append((self.text.index('>', self.absolute_position()) + 1, binding))
                break


def panel(route, title):
    embedded = route + '&embed=1'
    return ('\n<details class="dependency-panel" data-dependency-src="'
            + escape(embedded, quote=True) + '"><summary>Inspect dependencies</summary>'
            + '<p class="dependency-context">' + escape(title)
            + ' · compiled type and proof/definition references. '
            + '<a href="' + escape(route, quote=True)
            + '" target="_blank" rel="noopener">Open separately</a></p>'
            + '<div class="dependency-host"></div></details>\n')


def inject_panels(text, bindings, script, style):
    if 'data-dependency-panels="1"' in text:
        return text, 0
    parser = PanelPositions(text, bindings)
    parser.feed(text)
    for position, (route, title) in sorted(parser.inserts, reverse=True):
        text = text[:position] + panel(route, title) + text[position:]
    if parser.inserts:
        assets = ('<link rel="stylesheet" href="' + escape(style, quote=True) + '">'
                  '<script defer data-dependency-panels="1" src="'
                  + escape(script, quote=True) + '"></script>')
        if '</head>' not in text:
            raise ValueError('Dependency host page has no HTML head')
        text = text.replace('</head>', assets + '</head>', 1)
    return text, len(parser.inserts)


def add_dependency_views(site, templates):
    site, templates = Path(site), Path(templates)
    index = json.loads((site / 'structure/modules.json').read_text())
    owners = defaultdict(list)
    for shard in index['searchShards']:
        rows = json.loads((site / 'structure' / shard['path']).read_text())['declarations']
        for name, mid, kind in rows:
            owners[name].append((mid, kind))
    by_page = defaultdict(dict)

    def binding(page, name, mid, title):
        if mid not in {m for m, _ in owners[name]}:
            raise ValueError('Dependency route has no actual census provider: ' + name)
        target = posixpath.relpath(site / 'structure/index.html', page.parent)
        return target + '?' + urlencode({'module': mid, 'decl': name}), title

    api = json.loads((site / 'docs/declarations/declaration-data.bmp').read_text())
    for name, declaration in api['declarations'].items():
        parsed = urlsplit(declaration['docLink'])
        if parsed.scheme or parsed.netloc or name not in owners:
            continue
        providers = [(m, k) for m, k in owners[name] if k in {'theorem', 'definition', 'opaque'}]
        if not providers:
            continue
        relative = unquote(parsed.path).removeprefix('./')
        page = (site / 'docs' / relative).resolve()
        if not page.is_relative_to((site / 'docs').resolve()):
            raise ValueError('Unsafe API dependency host')
        module_name = '.'.join(Path(relative).with_suffix('').parts)
        mid = next((m for m, _ in providers if index['modules'][m]['name'] == module_name), providers[0][0])
        by_page[page][name] = binding(page, name, mid, name)
    projection = json.loads((site / 'structure/blueprint-projection.json').read_text())
    for page in [*(site / 'blueprint').glob('*.html'), *(site / 'report').glob('*.html')]:
        for node in projection['nodes']:
            if not node['modules']:
                raise ValueError('Selected mathematical node has no census provider')
            by_page[page][node['label']] = binding(page, node['name'], node['modules'][0], node['title'])
    counts = defaultdict(int)
    for page, bindings in by_page.items():
        text, count = inject_panels(page.read_text(), bindings,
            posixpath.relpath(site / 'dependency-panels.js', page.parent),
            posixpath.relpath(site / 'dependency-panels.css', page.parent))
        if count:
            page.write_text(text)
            counts[page.relative_to(site).parts[0]] += count
    for name in ('dependency-panels.js', 'dependency-panels.css'):
        shutil.copy2(templates / name, site / name)
    return dict(counts)
