#!/usr/bin/env python3
"""Refresh the reviewed Blueprint snapshot from actual rendered graph data.

The terminal list is an editorial contract, not inferred from arbitrary leaves.
Without --write this prints the checked inventory and preserves the snapshot.
"""
import argparse
import json
from pathlib import Path
import re

from verify_blueprint import validate_chapter, validate_terminals

ROOT = Path(__file__).resolve().parents[1]


def read_graph(path):
    import pygraphviz
    match = re.search(r'\.renderDot\(`(.*?)`\)', path.read_text(), re.S)
    if match is None:
        raise ValueError(f'Missing rendered graph: {path.name}')
    graph = pygraphviz.AGraph(match.group(1))
    return {'nodes': sorted(map(str, graph.nodes())),
            'edges': sorted([str(a), str(b)] for a, b in graph.edges())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--terminal', action='append',
                        help='Explicit approved exit; repeat for all exits when changing the contract')
    args = parser.parse_args()
    snapshot = ROOT / 'blueprint/graph.json'
    terminals = args.terminal or json.loads(snapshot.read_text())['terminals']
    graph = read_graph(ROOT / 'blueprint/web/dep_graph_document.html')
    catalog = json.loads((ROOT / 'blueprint/nodes.json').read_text())
    if graph['nodes'] != sorted(n['label'] for n in catalog):
        raise ValueError('Rendered graph does not match the complete selected catalogue')
    validate_terminals(graph['nodes'], graph['edges'], terminals)
    chapters = {}
    for path in sorted((ROOT / 'blueprint/web').glob('dep_graph_chapter_*.html')):
        chapter = read_graph(path)
        validate_chapter(chapter['nodes'], chapter['edges'], graph['nodes'], graph['edges'])
        chapters[path.name] = chapter
    if not chapters:
        raise ValueError('Missing chapter graphs')
    graph.update(chapters=chapters, terminals=sorted(terminals))
    if args.write:
        snapshot.write_text(json.dumps(graph, indent=2) + '\n')
    print(json.dumps({'nodes': len(graph['nodes']), 'edges': len(graph['edges']),
                      'chapters': len(chapters), 'terminals': graph['terminals'],
                      'snapshot_written': args.write}, indent=2))


if __name__ == '__main__':
    main()
