"""Selected Blueprint graph regression tests, independent of Graphviz installation."""
import unittest
from verify_blueprint import validate_graph


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

    def test_reversed_dependency(self):
        with self.assertRaisesRegex(ValueError, 'dependency edges'):
            validate_graph(self.expected['nodes'], [['endpoint', 'foundation']],
                           self.expected, self.expected['nodes'])


if __name__ == '__main__':
    unittest.main()
