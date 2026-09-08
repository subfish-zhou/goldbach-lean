#!/usr/bin/env python3
"""Validate the selected Blueprint graph and record its own source revision."""
from pathlib import Path
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
    if 'mathlib4_docs/find' in text:
        raise ValueError('Project source links point at the Mathlib documentation finder')
    source = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    report.update(source_revision=source, graph_scope='selected-chen-liliu-foundations')
    (ROOT / 'blueprint/web/build-info.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
