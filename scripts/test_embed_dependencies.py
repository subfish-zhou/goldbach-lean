"""Dependency panels preserve host markup and remain strictly on demand."""
import unittest
from embed_dependencies import inject_panels


class DependencyPanelTests(unittest.TestCase):
    def test_nested_block_and_apostrophe_anchor(self):
        text = '<html><head></head><body><div id="Example.fact\'"><div><br>type</div></div><p>after</p></body></html>'
        bindings = {"Example.fact'": ('../structure/index.html?module=1&decl=Example.fact%27', "Example.fact'")}
        result, count = inject_panels(text, bindings, '../dependency-panels.js', '../dependency-panels.css')
        self.assertEqual(count, 1)
        self.assertIn('<div><br>type</div></div>\n<details', result)
        self.assertLess(result.index('</details>'), result.index('<p>after</p>'))
        self.assertIn('&amp;embed=1', result)
        self.assertNotIn('<iframe', result)
        self.assertEqual(inject_panels(result, bindings, 'x', 'y'), (result, 0))

    def test_unknown_mathematical_target_fails(self):
        with self.assertRaisesRegex(ValueError, 'Unknown mathematical'):
            inject_panels('<div data-proof-node="missing"></div>', {}, 'x', 'y')

    def test_unselected_ids_are_unchanged(self):
        text = '<html><head></head><body><div id="other">x</div></body></html>'
        self.assertEqual(inject_panels(text, {}, 'x', 'y'), (text, 0))

    def test_math_placeholder_and_escaped_title(self):
        text = '<html><head></head><body><div data-proof-node="bp:stage"></div></body></html>'
        result, count = inject_panels(text, {'bp:stage': ('../structure/index.html?module=2&decl=x', 'A < B')}, 'x', 'y')
        self.assertEqual(count, 1)
        self.assertIn('A &lt; B', result)
        self.assertNotIn('<iframe', result)


if __name__ == '__main__':
    unittest.main()
