"""Bounded type-symbol retrieval; similarity is never an admission certificate."""
import json
import math
from collections import Counter, defaultdict


class TypeFeatures:
    """Retrieve same-conclusion candidates without requiring equal binder shapes.

    Inverse-frequency weighted cosine similarity ranks *type* constants. This
    does not unify types, discharge premises, or prove general-to-special reuse.
    Declaration/import dependency gates and actual Lean coverage remain required.
    """

    def __init__(self, rows):
        self.rows = {r['name']: r for r in rows}
        self.symbols = {}
        self.postings = defaultdict(set)
        counts = Counter()
        noise = {'Nat', 'Int', 'Real', 'Prop', 'Exists', 'And', 'Eq', 'LE.le',
                 'LT.lt', 'OfNat.ofNat', 'Nat.cast', 'Int.cast', 'Classical.choice'}
        for name, row in self.rows.items():
            symbols = set(json.loads(row['payload'])['type_deps']) - noise
            symbols = {s for s in symbols if not s.startswith('_private.')
                       and '.inst' not in s and not s.startswith('inst')}
            self.symbols[name] = symbols
            counts.update(symbols)
            for symbol in symbols:
                self.postings[(row['conclusion_head'], symbol)].add(name)
        self.weights = {s: math.log1p(len(rows) / n) for s, n in counts.items()}
        self.mass = {name: sum(self.weights[s] for s in sorted(symbols))
                     for name, symbols in self.symbols.items()}

    def matches(self, target, limit=8):
        if limit < 1:
            raise ValueError('positive provider limit required')
        name = target['name']
        scores, shared = defaultdict(float), Counter()
        for symbol in sorted(self.symbols[name]):
            for other in self.postings[(target['conclusion_head'], symbol)]:
                if other == name:
                    continue
                scores[other] += self.weights[symbol]
                shared[other] += 1
        found = []
        for other, numerator in scores.items():
            if shared[other] < 2:
                continue
            score = numerator / math.sqrt(self.mass[name] * self.mass[other])
            found.append((score, other))
        return [(self.rows[other], score) for score, other in
                sorted(found, key=lambda item: (-item[0], item[1]))[:limit]]
