"""Selected Blueprint graph regression tests, independent of Graphviz installation."""
import unittest
import tempfile
from pathlib import Path
from verify_blueprint import validate_graph, validate_chapter, validate_terminals, reader_routes


class BlueprintGraphTests(unittest.TestCase):
    def setUp(self):
        self.expected = {'nodes': ['foundation', 'endpoint'],
                         'edges': [['foundation', 'endpoint']]}

    def test_exact_graph(self):
        self.assertEqual(validate_graph(self.expected['nodes'], self.expected['edges'],
                                        self.expected, self.expected['nodes']),
                         {'node_count': 2, 'edge_count': 1})

    def test_missing_node(self):
        with self.assertRaisesRegex(ValueError, 'node inventory'):
            validate_graph(['endpoint'], [], self.expected, self.expected['nodes'])

    def test_omitted_annotation(self):
        with self.assertRaisesRegex(ValueError, 'node inventory'):
            validate_graph(self.expected['nodes'], self.expected['edges'],
                           self.expected, ['foundation'])

    def test_chapter_edge_has_a_real_path(self):
        validate_chapter(['a', 'c'], [('a', 'c')], ['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])

    def test_chapter_cannot_invent_a_dependency(self):
        with self.assertRaisesRegex(ValueError, 'no compiled dependency path'):
            validate_chapter(['a', 'c'], [('c', 'a')], ['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])

    def test_chapter_cannot_invent_a_node(self):
        with self.assertRaisesRegex(ValueError, 'undocumented declaration'):
            validate_chapter(['a', 'x'], [], ['a'], [])

    def test_reader_routes_follow_ids_and_are_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for topic in ['overview', 'foundations', 'chen', 'liliu']:
                (root / ('generated-' + topic + '.html')).write_text('<h1 id="chap:' + topic + '">Title</h1>')
            first = reader_routes(root)
            self.assertEqual(first['chen.html'], 'generated-chen.html')
            self.assertEqual((root / 'chen.html').read_bytes(), (root / 'generated-chen.html').read_bytes())
            self.assertEqual(reader_routes(root), first)

    def test_missing_reader_chapter_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, 'Missing chapter anchor'):
                reader_routes(Path(tmp))

    def test_all_nodes_reach_documented_exits(self):
        validate_terminals(['a', 'b', 'c'], [('a', 'b'), ('b', 'c')], ['c'])

    def test_unused_selected_lemma_is_rejected(self):
        with self.assertRaises(ValueError):
            validate_terminals(['a', 'b', 'unused'], [('a', 'b')], ['b'])

    def test_disconnected_cycle_is_rejected(self):
        with self.assertRaises(ValueError):
            validate_terminals(['a', 'b', 'c'], [('a', 'b'), ('b', 'a')], ['c'])

    def test_reversed_dependency(self):
        with self.assertRaisesRegex(ValueError, 'dependency edges'):
            validate_graph(self.expected['nodes'], [['endpoint', 'foundation']],
                           self.expected, self.expected['nodes'])


if __name__ == '__main__':
    unittest.main()
