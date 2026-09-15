

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

/-- Exact production bridge for the literal `(2.1)` ledger.  The source weight
`1 / φ(q)` is first increased to `q / φ(q)` and only then is the proved
primitive Gauss--Farey large sieve invoked. -/
theorem panTheoremALeft_le_productionFareyBound
    (b : ℤ → ℂ) (M : ℤ) (N P Q : ℕ) (hP : 0 < P) (hPQ : P < Q) :
    panTheoremALeft b M N P Q ≤
      largeSieveBound N (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have hQ : 0 < Q := hP.trans hPQ
  calc
    panTheoremALeft b M N P Q ≤
        ∑ q ∈ Finset.Ioc P Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 := by
      unfold panTheoremALeft
      apply Finset.sum_le_sum
      intro q hq
      have hqP := (Finset.mem_Ioc.mp hq).1
      have hqpos : 0 < q := hP.trans hqP
      have hsum : 0 ≤ ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 := by positivity
      have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
      have hcoeff : (q.totient : ℝ)⁻¹ ≤
          (q : ℝ) * (q.totient : ℝ)⁻¹ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hqone (by positivity : 0 ≤ (q.totient : ℝ)⁻¹)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hcoeff hsum
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rcases Finset.mem_Ioc.mp hq with ⟨hqP, hqQ⟩
        exact Finset.mem_Icc.mpr ⟨by omega, hqQ⟩
      · intro q hq hnot
        positivity
    _ ≤ _ := weightedPrimitiveSquareLedger_largeSieve b M N Q hQ

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

/-- Exact low/high conductor partition `(2.9)`. -/
theorem panIym_eq_low_add_high
    (g d : ℕ → ℂ) (y A₁ A₂ D₁ D : ℕ) (hD : D₁ ≤ D) :
    panIym g d y A₁ A₂ D =
      panIymLow g d y A₁ A₂ D₁ + panIymHigh g d y A₁ A₂ D₁ D := by
  have hset : Finset.Icc 1 D = Finset.Icc 1 D₁ ∪ Finset.Ioc D₁ D := by
    ext q
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 1 D₁) (Finset.Ioc D₁ D) := by
    refine Finset.disjoint_left.mpr ?_
    intro q hq₁ hq₂
    exact (not_lt_of_ge (Finset.mem_Icc.mp hq₁).2) (Finset.mem_Ioc.mp hq₂).1
  unfold panIym panIymLow panIymHigh
  rw [hset, Finset.sum_union hdis]

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