

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualDecomposition

/-!
 # Physical AP-normalized bounds for actual Vaughan Type-II shells

This file starts with the genuine collected hyperbolic-prefix maximum.  It applies
prefix-maximal large sieve row by row, sums the rows after paying the Möbius
energy, and only then uses Cauchy in primitive characters and moduli.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Primitive characters form a subtype of all characters, whose cardinality is
`φ(q)`.  This discharges the elementary cardinality side condition in direct
Cauchy estimates. -/
theorem card_primitiveCharacter_le_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  exact primitiveCharacter_card_le_totient_basic q hq


end

end AnalyticNumberTheory.LargeSieve
