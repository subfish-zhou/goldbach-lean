

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

/-- The literal primitive-character square ledger on `P < q ≤ Q` occurring on
the left of Pan--Wang--Ding Theorem A `(2.1)`. -/
def panTheoremALeft
    (b : ℤ → ℂ) (M : ℤ) (N P Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc P Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ‖primitiveIntervalAmplitude b M N χ‖ ^ 2


/-! ## Equations (2.7), (2.9)--(2.11), and the literal `(2.14)` cell -/

/-- The complete source/product character amplitude inside the absolute value
in `(2.7)`.  The inner cutoff depends on `a`, and cancellation across the whole
outer `a`-sum is retained. -/
def panSourceCharacterAmplitude {q : ℕ}
    (g d : ℕ → ℂ) (y A₁ A₂ : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ a ∈ Finset.Ioc A₁ A₂,
    g a * χ.1 (a : ZMod q) *
      ∑ n ∈ Finset.Icc 1 (y / a), d n * χ.1 (n : ZMod q)

/-- Pan--Wang--Ding `(2.7)`, with the absolute value outside the complete
`a`-sum. -/
def panIym
    (g d : ℕ → ℂ) (y A₁ A₂ D : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 D, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ‖panSourceCharacterAmplitude g d y A₁ A₂ χ‖

/-- The low-conductor term `(2.10)`. -/
def panIymLow
    (g d : ℕ → ℂ) (y A₁ A₂ D₁ : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 D₁, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ‖panSourceCharacterAmplitude g d y A₁ A₂ χ‖

/-- The high-conductor term `(2.11)`. -/
def panIymHigh
    (g d : ℕ → ℂ) (y A₁ A₂ D₁ D : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D₁ D, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ‖panSourceCharacterAmplitude g d y A₁ A₂ χ‖


/-- Literal dyadic block `(2.14)`.  Both the modulus cell and source cell are
left explicit, and the norm still surrounds the complete source sum. -/
def panIymDyadicBlock
    (g d : ℕ → ℂ) (y D₁ A₁ : ℕ) (j k : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc (2 ^ j * D₁) (2 ^ (j + 1) * D₁),
    ((q.totient : ℝ)⁻¹) *
      ∑ χ : PrimitiveCharacter q,
        ‖panSourceCharacterAmplitude g d y
          (2 ^ k * A₁) (2 ^ (k + 1) * A₁) χ‖

end

end AnalyticNumberTheory.LargeSieve