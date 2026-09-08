"""Source-linked, chapter-sized views of compiled declaration dependencies."""
from pathlib import Path
import json
import re
import subprocess
import textwrap
import html
from urllib.parse import quote


def decorate_graph(text, heading, caption):
    text, n = re.subn(r'<h1[^>]*>.*?</h1>', '<h1>' + html.escape(heading) + '</h1>',
                      text, count=1, flags=re.S)
    if n != 1:
        raise ValueError('Graph header is missing')
    text = re.sub(r'<title>.*?</title>', '<title>' + html.escape(heading) + '</title>',
                  text, count=1, flags=re.S)
    paragraph = '<p id="graph-reading-guide" style="margin:1rem;max-width:75ch">' + html.escape(caption) + '</p>'
    if 'id="graph-reading-guide"' in text:
        text = re.sub(r'<p id="graph-reading-guide"[^>]*>.*?</p>', paragraph, text, count=1, flags=re.S)
    else:
        text = text.replace('</header>', '</header>\n' + paragraph, 1)
    return text


def reader_label(title):
    """Use mathematical titles, keeping internal labels only as identifiers."""
    return r'\n'.join(textwrap.wrap(title.replace('--', '–'), width=26,
                                    break_on_hyphens=False, break_long_words=False))


def chapter_slice(nodes, edges, proof_edges, local):
    """Include immediate external inputs; never create a new dependency edge."""
    local = set(local) & set(nodes)
    combined = set(edges) | set(proof_edges)
    external = {a for a, b in combined if b in local and a not in local}
    selected = local | external
    return (selected, {(a, b) for a, b in edges if a in selected and b in selected},
            {(a, b) for a, b in proof_edges if a in selected and b in selected}, external)


def project_paths(nodes, edges, selected):
    """Collapse existing paths between overview nodes, preserving reachability."""
    selected = set(selected) & set(nodes)
    adjacency = {node: set() for node in nodes}
    for a, b in edges:
        adjacency[a].add(b)
    projected = set()
    for start in selected:
        pending, seen = list(adjacency[start]), set()
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            seen.add(node)
            pending.extend(adjacency[node] - seen)
        projected.update((start, end) for end in (seen & selected) - {start})
    return selected, projected


def ProcessOptions(options, document):
    from plasTeX.PackageResource import PackageCss, PackagePreCleanupCB
    document.addPackageResource(PackageCss(path=Path(__file__).with_name('reader.css')))
    graph_headings = {}

    def graph_captions(doc):
        for filename, (heading, caption) in graph_headings.items():
            path = Path(filename)
            path.write_text(decorate_graph(path.read_text(), heading, caption))
        return []
    document.addPackageResource(PackagePreCleanupCB(data=graph_captions))
    root = Path(__file__).resolve().parents[2]
    revision = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=root, text=True
    ).strip()
    document.context.newcommand('sourcefile', 2,
        r'\href{https://github.com/subfish-zhou/goldbach-lean/blob/' + revision + r'/#1}{#2}')
    catalog = json.loads((root / 'blueprint/nodes.json').read_text())
    titles = {node['label']: node['title'] for node in catalog}
    chapters = {node['label']: node['chapter'] for node in catalog}

    def readable_graphs():
        graphs = document.userdata['dep_graph']['graphs']
        original = graphs[document]
        base = type(original)

        class ReaderGraph(base):
            external = frozenset()

            def to_dot(self, shapes):
                dot = super().to_dot(shapes)
                for node in self.nodes:
                    title = titles[node.id]
                    label = reader_label(title)
                    if node in self.external:
                        label += r'\n(input)'
                    dot.get_node(node.id).attr['label'] = label
                for group, heading in [('foundations', 'Analytic inputs'),
                                       ('chen', 'Chen 1 + 2'), ('liliu', 'Li–Liu 1 + 1.9')]:
                    members = [node.id for node in self.nodes if chapters.get(node.id) == group]
                    if members:
                        dot.add_subgraph(members, name='cluster_' + group, label=heading,
                                         color='#64748b', fontsize='16', fontname='Helvetica',
                                         style='rounded', margin='16')
                dot.graph_attr.update(ranksep='0.6', nodesep='0.3')
                return dot

        def make(nodes, edges, proof_edges, external=frozenset()):
            graph = ReaderGraph()
            graph.document = document
            graph.nodes = set(nodes)
            graph.edges = set(edges)
            graph.proof_edges = set(proof_edges)
            graph.external = frozenset(external)
            return graph

        graphs[document] = make(original.nodes, original.edges, original.proof_edges)
        graph_headings['dep_graph_document.html'] = ('All documented proof dependencies',
            'The full selected declaration graph. Each node opens its mathematical statement and Lean source. Use the chapter graphs for a smaller view.')
        for item in document.rendererdata['html5']['extra_toc_items']:
            if item['url'] == 'dep_graph_document.html':
                item['text'] = 'All documented lemmas — proof graph'
        overview_labels = {item['label'] for item in catalog if item.get('overview')}
        for chapter in document.getElementsByTagName('chapter'):
            local = set()
            for kind in document.userdata['dep_graph']['thm_types']:
                local.update(chapter.getElementsByTagName(kind))
            local &= original.nodes
            if chapter.id == 'chap:overview' and overview_labels:
                selected, paths = project_paths(original.nodes, original.edges | original.proof_edges,
                    {node for node in original.nodes if node.id in overview_labels})
                graphs[chapter] = make(selected, set(), paths)
            elif local:
                selected, edges, proof_edges, external = chapter_slice(
                    original.nodes, original.edges, original.proof_edges, local)
                graphs[chapter] = make(selected, edges, proof_edges, frozenset(external))
            else:
                continue
            target = 'dep_graph_' + chapter.counter + '_' + chapter.ref.textContent + '.html'
            title = chapter.title.textContent
            heading = {'chap:overview': 'Proof-route overview', 'chap:foundations': 'Analytic foundations',
                       'chap:chen': 'Chen proof dependencies', 'chap:liliu': 'Li–Liu proof dependencies'}.get(chapter.id, title)
            caption = ('Arrows compress existing compiled dependency paths between major stages. Open the proof chapters to expand the intermediate estimates.' if chapter.id == 'chap:overview'
                       else 'Arrows follow compiled declaration dependencies. Nodes marked (input) are introduced in another chapter. Click a node for its statement and Lean source.')
            graph_headings[target] = (heading, caption)
            document.rendererdata['html5']['extra_toc_items'].append(
                {'text': title + ' — proof graph', 'url': target})

    def source_links():
        locations = {}
        artifacts = root / '.lake/build/blueprint/module/Goldbach/Blueprint.artifacts'
        for path in artifacts.glob('*.tex'):
            match = re.search(r'\\lean\{([^}]+)\}\s*% at (.+):(\d+)\.\d+-', path.read_text())
            if match:
                declaration, source, line = match.groups()
                relative = Path(source).resolve().relative_to(root)
                locations[declaration] = (
                    'https://github.com/subfish-zhou/goldbach-lean/blob/'
                    f'{revision}/{quote(relative.as_posix())}#L{int(line) + 1}')
        for graph in document.userdata['dep_graph']['graphs'].values():
            for node in graph.nodes:
                declarations = node.userdata.get('leandecls', [])
                node.userdata['lean_urls'] = [(decl, locations[decl]) for decl in declarations]

    document.addPostParseCallbacks(150, readable_graphs)
    document.addPostParseCallbacks(160, source_links)
