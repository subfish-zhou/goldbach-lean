

import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveGaussFareyExactBridge

/-!
 # Pan--Wang--Ding (1975), early source reductions

This module records the first literal finite objects in the proof of Theorem 2
on pp. 600--602.  In particular, the absolute value in `(2.7)`, `(2.10)`,
`(2.11)`, and `(2.14)` surrounds the complete `a`-sum.  No termwise absolute
majorant is introduced here.

The paper's Theorem A `(2.1)` has the sharper classical factor
`Q + N / P` (up to an absolute constant).  The first theorem below only connects
its literal left side to the unconditional reduced-Farey large-sieve factor
currently proved in production; it does not rename that weaker factor as the
paper's source estimate.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-! ## Theorem A, equation (2.1): literal left side -/


/-! ## Equations (2.7), (2.9)--(2.11), and the literal `(2.14)` cell -/

/-- The complete source/product character amplitude inside the absolute value
in `(2.7)`.  The inner cutoff depends on `a`, and cancellation across the whole
outer `a`-sum is retained. -/
def panSourceCharacterAmplitude {q : ℕ}
    (g d : ℕ → ℂ) (y A₁ A₂ : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ a ∈ Finset.Ioc A₁ A₂,
    g a * χ.1 (a : ZMod q) *
      ∑ n ∈ Finset.Icc 1 (y / a), d n * χ.1 (n : ZMod q)


/-- The high-conductor term `(2.11)`. -/
def panIymHigh
    (g d : ℕ → ℂ) (y A₁ A₂ D₁ D : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D₁ D, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ‖panSourceCharacterAmplitude g d y A₁ A₂ χ‖


end

end AnalyticNumberTheory.LargeSieve