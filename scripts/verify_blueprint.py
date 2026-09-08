#!/usr/bin/env python3
"""Validate the selected Blueprint graph and record its own source revision."""
from pathlib import Path
from html.parser import HTMLParser
import shutil
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def validate_graph(nodes, edges, expected, annotated) -> dict[str, object]:
    nodes = set(nodes)
    edges = {tuple(e) for e in edges}
    if nodes != set(expected['nodes']) or nodes != set(annotated):
        raise ValueError('Blueprint node inventory disagrees with annotations or specification')
    if edges != {tuple(e) for e in expected['edges']}:
        raise ValueError('Blueprint dependency edges changed')
    return {'node_count': len(nodes), 'edge_count': len(edges)}


def validate_chapter(nodes, edges, full_nodes, full_edges):
    """Every chapter edge must follow a compiled path in the full projection."""
    nodes = set(nodes)
    full_nodes = set(full_nodes)
    if not nodes <= full_nodes:
        raise ValueError('Chapter graph has an undocumented declaration')
    adjacency = {node: set() for node in full_nodes}
    for a, b in full_edges:
        adjacency[a].add(b)
    for a, b in edges:
        if a not in nodes or b not in nodes:
            raise ValueError('Chapter edge leaves its node inventory')
        pending, seen = list(adjacency[a]), set()
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            pending.extend(adjacency[current] - seen)
        if b not in seen:
            raise ValueError('Chapter edge has no compiled dependency path')


def validate_terminals(nodes, edges, terminals):
    """Reject selected lemmas that have no compiled path to a theorem exit."""
    nodes, terminals = set(nodes), set(terminals)
    if nodes - {a for a, _ in edges} != terminals:
        raise ValueError('Blueprint has an unexpected or missing theorem exit')
    seen, pending = set(terminals), list(terminals)
    while pending:
        target = pending.pop()
        for source, consumer in edges:
            if consumer == target and source not in seen:
                seen.add(source)
                pending.append(source)
    if seen != nodes:
        raise ValueError('A selected lemma does not support a theorem exit')


def reader_routes(directory):
    """Stable chapter routes, resolved from rendered IDs rather than page numbers."""
    class Ids(HTMLParser):
        def __init__(self):
            super().__init__()
            self.ids = set()

        def handle_starttag(self, tag, attrs):
            self.ids.update(value for name, value in attrs if name == 'id')

    aliases = {'chap:overview': 'overview.html', 'chap:foundations': 'foundations.html',
               'chap:chen': 'chen.html', 'chap:liliu': 'liliu.html'}
    found = {}
    for page in directory.glob('*.html'):
        if page.name in aliases.values() or page.name.startswith('dep_graph_'):
            continue
        parser = Ids()
        parser.feed(page.read_text())
        for label in parser.ids & aliases.keys():
            if label in found:
                raise ValueError('Duplicate chapter anchor: ' + label)
            found[label] = page
    if set(found) != set(aliases):
        raise ValueError('Missing chapter anchor for reader routes')
    for label, alias in aliases.items():
        shutil.copy2(found[label], directory / alias)
    return {alias: found[label].name for label, alias in aliases.items()}


def verify_sourcefiles(root):
    paths = set()
    for path in (root / 'blueprint/src/chapters').glob('*.tex'):
        paths.update(re.findall(r'\\sourcefile\{([^}]+)\}', path.read_text()))
    for relative in paths:
        path = (root / relative).resolve()
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            raise ValueError('Missing or out-of-project Blueprint source path: ' + relative)
    return sorted(paths)


def main():
    import pygraphviz
    page = ROOT / 'blueprint/web/dep_graph_document.html'
    text = page.read_text()
    match = re.search(r'\.renderDot\(`(.*?)`\)', text, re.S)
    if match is None:
        raise ValueError('Rendered dependency graph is missing')
    graph = pygraphviz.AGraph(match.group(1))
    annotated = re.findall(r'attribute\s*\[blueprint\s+"([^"]+)"',
                           (ROOT / 'Goldbach/Blueprint.lean').read_text())
    if len(annotated) != len(set(annotated)):
        raise ValueError('Duplicate Blueprint annotation label')
    expected = json.loads((ROOT / 'blueprint/graph.json').read_text())
    report = validate_graph([str(n) for n in graph.nodes()],
                            [list(e) for e in graph.edges()], expected, annotated)
    validate_terminals([str(n) for n in graph.nodes()], [list(e) for e in graph.edges()], expected['terminals'])
    catalog = json.loads((ROOT / 'blueprint/nodes.json').read_text())
    from generate_blueprint import generate
    if generate(catalog) != (ROOT / 'Goldbach/Blueprint.lean').read_text():
        raise ValueError('Lean annotations are out of sync with the mathematical catalogue')
    titles = {node['label']: node['title'] for node in catalog}
    if set(titles) != set(annotated):
        raise ValueError('Blueprint catalog differs from the compiled annotation selection')
    for node in graph.nodes():
        display = str(node.attr['label']).replace('\\n', ' ').replace('\n', ' ')
        if display != titles[str(node)].replace('--', '–'):
            raise ValueError('Graph node does not display its mathematical title')
    chapter_pages = sorted((ROOT / 'blueprint/web').glob('dep_graph_chapter_*.html'))
    chapter_specs = expected.get('chapters', {})
    if {p.name for p in chapter_pages} != set(chapter_specs):
        raise ValueError('Chapter graph route inventory changed')
    chapter_reports = {}
    for path in chapter_pages:
        chapter_text = path.read_text()
        chapter_match = re.search(r'\.renderDot\(`(.*?)`\)', chapter_text, re.S)
        if chapter_match is None:
            raise ValueError('Rendered chapter graph is missing')
        chapter = pygraphviz.AGraph(chapter_match.group(1))
        nodes = [str(n) for n in chapter.nodes()]
        edges = [list(e) for e in chapter.edges()]
        chapter_reports[path.name] = validate_graph(nodes, edges, chapter_specs[path.name], nodes)
        validate_chapter(nodes, edges, [str(n) for n in graph.nodes()], [list(e) for e in graph.edges()])
    if 'mathlib4_docs/find' in text:
        raise ValueError('Project source links point at the Mathlib documentation finder')
    source = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    report.update(source_revision=source, graph_scope='mathematical-routes-with-chapter-inputs',
                  chapters=chapter_reports, reader_routes=reader_routes(ROOT / 'blueprint/web'),
                  sourcefile_paths=verify_sourcefiles(ROOT))
    (ROOT / 'blueprint/web/build-info.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
