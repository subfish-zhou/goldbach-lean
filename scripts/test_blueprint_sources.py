"""Reader labels and chapter projections preserve the extracted dependency graph."""
from pathlib import Path
import importlib.util
import unittest
import tempfile

SOURCE = Path(__file__).resolve().parents[1] / 'blueprint/src/sources.py'
SPEC = importlib.util.spec_from_file_location('blueprint_sources', SOURCE)
assert SPEC and SPEC.loader
sources = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sources)


class ChapterGraphTests(unittest.TestCase):
    def test_relocated_source_requires_exact_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / 'checkout'
            root.mkdir()
            target = root / 'Example.lean'
            recorded = Path(tmp) / 'original.lean'
            target.write_text('theorem example : True := True.intro')
            recorded.write_bytes(target.read_bytes())
            self.assertEqual(sources.verified_source_path(root, recorded, 'Example.lean'),
                             Path('Example.lean'))
            recorded.write_text('different source')
            with self.assertRaises(ValueError):
                sources.verified_source_path(root, recorded, 'Example.lean')
            with self.assertRaises(ValueError):
                sources.verified_source_path(root, recorded, '../original.lean')

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


class DeclarationLineTests(unittest.TestCase):
    """Exported declaration positions resolve to the line that opens them."""

    def test_bare_declaration_keeps_its_recorded_line(self):
        lines = ['namespace Demo', '', 'theorem demo : True := trivial']
        self.assertEqual(sources.declaration_line(lines, 3), 3)

    def test_single_line_doc_comment_advances_to_the_declaration(self):
        lines = ['/-- A short note. -/', 'theorem demo : True := trivial']
        self.assertEqual(sources.declaration_line(lines, 1), 2)

    def test_multi_line_doc_comment_advances_to_the_declaration(self):
        lines = ['/-- A longer note,', 'spanning several lines. -/', '',
                 'theorem demo : True :=', '  trivial']
        self.assertEqual(sources.declaration_line(lines, 1), 4)

    def test_declaration_after_a_closing_comment_line(self):
        lines = ['/-- Note. -/', '', '', 'def demo : Nat := 0']
        self.assertEqual(sources.declaration_line(lines, 1), 4)

    def test_nested_comment_and_inline_declaration(self):
        lines = ['/- outer /- inner -/ still outer -/ theorem demo : True := trivial']
        self.assertEqual(sources.declaration_line(lines, 1), 1)

    def test_recorded_line_outside_the_source_is_rejected(self):
        with self.assertRaises(ValueError):
            sources.declaration_line(['theorem demo : True := trivial'], 9)
        with self.assertRaises(ValueError):
            sources.declaration_line(['theorem demo : True := trivial'], 0)

    def test_unterminated_comment_is_rejected(self):
        with self.assertRaises(ValueError):
            sources.declaration_line(['/-- never closed'], 1)

    def test_comment_without_a_following_declaration_is_rejected(self):
        with self.assertRaises(ValueError):
            sources.declaration_line(['/-- Note. -/', '', ''], 1)


if __name__ == '__main__':
    unittest.main()
