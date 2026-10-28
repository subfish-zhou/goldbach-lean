

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectL1Physical

/-!
 # Unconditional closure of the actual dyadic Vaughan Type-I input
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section


/-- Primitive characters form a subtype of all Dirichlet characters, so their
cardinality is bounded by Euler's totient without any additional hypothesis. -/
theorem card_primitiveCharacter_le_totient (q : ℕ) :
    0 < q → Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  intro hq
  exact primitiveCharacter_card_le_totient_basic q hq


end

end AnalyticNumberTheory.LargeSieve
