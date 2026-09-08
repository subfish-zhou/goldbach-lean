import json
from pathlib import Path
import unittest
from generate_blueprint import generate

ROOT = Path(__file__).resolve().parents[1]


class GeneratedAnnotations(unittest.TestCase):
    def test_committed_annotations_match_catalogue(self):
        nodes = json.loads((ROOT / 'blueprint/nodes.json').read_text())
        self.assertEqual((ROOT / 'Goldbach/Blueprint.lean').read_text(), generate(nodes))

    def test_duplicate_labels_are_rejected(self):
        node = dict(label='a', declaration='A', title='A', statement='$a$')
        with self.assertRaises(ValueError):
            generate([node, dict(node, declaration='B')])

    def test_control_characters_are_rejected(self):
        node = dict(label='a', declaration='A', title='A', statement='bad\rtext')
        with self.assertRaises(ValueError):
            generate([node])


if __name__ == '__main__':
    unittest.main()
