"""Reader labels and chapter projections preserve the extracted dependency graph."""
from pathlib import Path
import importlib.util
import unittest

SOURCE = Path(__file__).resolve().parents[1] / 'blueprint/src/sources.py'
SPEC = importlib.util.spec_from_file_location('blueprint_sources', SOURCE)
assert SPEC and SPEC.loader
sources = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sources)


class ChapterGraphTests(unittest.TestCase):
    def test_projection_keeps_inputs_without_fabricating_edges(self):
        nodes = {'background', 'input', 'middle', 'endpoint', 'other'}
        edges = {('background', 'input')}
        proof = {('input', 'middle'), ('middle', 'endpoint'), ('input', 'other')}
        selected, typ, prf, external = sources.chapter_slice(
            nodes, edges, proof, {'middle', 'endpoint'})
        self.assertEqual(selected, {'input', 'middle', 'endpoint'})
        self.assertEqual(external, {'input'})
        self.assertEqual(typ, set())
        self.assertEqual(prf, {('input', 'middle'), ('middle', 'endpoint')})
        self.assertNotIn(('input', 'endpoint'), prf)
        self.assertEqual(len(proof), 3)

    def test_overview_collapses_only_existing_paths(self):
        selected, edges = sources.project_paths({'a', 'b', 'c', 'x'},
                                                {('a', 'b'), ('b', 'c')}, {'a', 'c', 'x'})
        self.assertEqual(selected, {'a', 'c', 'x'})
        self.assertEqual(edges, {('a', 'c')})

    def test_empty_chapter_has_no_nodes(self):
        self.assertEqual(sources.chapter_slice({'a'}, set(), set(), set()),
                         (set(), set(), set(), set()))

    def test_graph_caption_is_escaped_and_idempotent(self):
        text = '<title>Dependency graph</title><header><h1>Dependencies</h1></header><script>unchanged</script>'
        once = sources.decorate_graph(text, 'A & B', 'Paths, not direct edges.')
        self.assertIn('A &amp; B', once)
        self.assertEqual(once, sources.decorate_graph(once, 'A & B', 'Paths, not direct edges.'))
        self.assertEqual(once.count('id="graph-reading-guide"'), 1)
        self.assertIn('<script>unchanged</script>', once)

    def test_natural_title_is_wrapped_not_replaced_by_identifier(self):
        title = 'Jurkat--Richert weighted lower sieve'
        label = sources.reader_label(title)
        self.assertEqual(label.replace(r'\n', ' '), title.replace('--', '–'))
        self.assertTrue(all(len(line) <= 26 for line in label.split(r'\n')))


if __name__ == '__main__':
    unittest.main()
