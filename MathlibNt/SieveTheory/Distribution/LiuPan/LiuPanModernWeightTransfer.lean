import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanActualErrorEnvelope
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969BombieriWeightPayment

/-! The only analytic input below is the explicitly conditional unweighted
Pan (1975) Theorem 2 specialization for the actual convolution error.
The weight payment is modern finite Cauchy, as in Maynard Lemma 5.2 (5.19)--(5.20).
It is not an application of ordinary prime Bombieri--Vinogradov to a convolution. -/
noncomputable section
open Finset Filter
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiuWeight

/-- Exactly the same interval, normalization and residue maximum as the weighted source. -/
def liuPanActualError (κ : ℝ) (N : ℕ) (B : ℝ) (q : ℕ) : ℝ :=
  liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N
    (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
    (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

theorem liuPanActualError_nonneg (κ : ℝ) (N : ℕ) (B : ℝ) (q : ℕ) :
    0 ≤ liuPanActualError κ N B q := liuMainPanCoprimeIntervalMaxL_nonneg ..

/-- The actual source mass with both μ² and 3^ω removed, not a prime discrepancy. -/
def liuPanUnweightedTheorem2Sum (κ : ℝ) (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panSourceStrictModulusCutoff N B), liuPanActualError κ N B q

/-- Still-unproved analytic input: a Liu specialization of Pan (1975), Theorem 2.
κ is fixed before U; U is the saving exponent, not the cutoff exponent B. -/
def LiuPanUnweightedTheorem2Specialization : Prop :=
  ∃ κ : ℝ, ∀ U : ℝ, 0 < U →
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPanUnweightedTheorem2Sum κ N B ≤ C * N / Real.log N ^ U

def liuPanSquarefreeCarrier (N : ℕ) (B : ℝ) : Finset ℕ :=
  (range (panSourceStrictModulusCutoff N B)).filter Squarefree

theorem liuPanWeightedSum_eq_squarefree (κ : ℝ) (N : ℕ) (B : ℝ) :
    liuPanWangDingCorollary230Sum κ N B =
      Richert1969.threeOmegaErrorMass (liuPanSquarefreeCarrier N B)
        (liuPanActualError κ N B) := by
  classical
  unfold liuPanWangDingCorollary230Sum Richert1969.threeOmegaErrorMass liuPanSquarefreeCarrier
  rw [sum_filter]
  apply sum_congr rfl
  intro q _
  by_cases hq : Squarefree q
  · rw [if_pos hq, SwitchingPrinciple.moebius_sq_eq_one_of_squarefree hq, one_mul]
    rfl
  · rw [if_neg hq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
    simp

theorem panSourceStrictModulusCutoff_mem_le {N q : ℕ} {B : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B)
    (hq : q ∈ range (panSourceStrictModulusCutoff N B)) : q ≤ N := by
  have hqR := (mem_range_panSourceStrictModulusCutoff_iff q N B).mp hq
  have hden : 1 ≤ Real.log (N : ℝ) ^ B := Real.one_le_rpow hlog hB
  have hroot : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ N by exact_mod_cast hN) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hbound : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B ≤ N :=
    (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg N) _) hden).trans hroot
  exact_mod_cast (hqR.trans_le hbound).le

theorem liuPanSquarefreeCarrier_subset {N : ℕ} {B : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    liuPanSquarefreeCarrier N B ⊆ range (N + 1) := by
  intro q hq
  have hq_le := panSourceStrictModulusCutoff_mem_le hN hlog hB (mem_filter.mp hq).1
  exact mem_range.mpr (Nat.lt_succ_of_le hq_le)

theorem liuPanSquarefreeErrorSum_le_unweighted (κ : ℝ) (N : ℕ) (B : ℝ) :
    (∑ q ∈ liuPanSquarefreeCarrier N B, liuPanActualError κ N B q) ≤
      liuPanUnweightedTheorem2Sum κ N B := by
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro q _ _
  exact liuPanActualError_nonneg κ N B q

/-- A single global ninth-moment constant is fixed before κ,N,B.
No distribution assumption or extra envelope hypothesis remains in this finite theorem. -/
theorem exists_liuPanWeightedSum_sq_le_unweighted :
    ∃ C₉ : ℝ, 0 < C₉ ∧ ∀ (κ : ℝ) (N : ℕ) (B : ℝ),
      2 ≤ N → 1 ≤ Real.log (N : ℝ) → 0 ≤ B →
      liuPanWangDingCorollary230Sum κ N B ^ 2 ≤
        (C₉ * Real.log (N + 2) ^ (9 : ℝ)) *
          ((liuActualEnvelopeConstant κ * N * (1 + Real.log N) ^ 2) *
            liuPanUnweightedTheorem2Sum κ N B) := by
  obtain ⟨C₉, hC₉, hmoment⟩ := Richert1969.lemma3NineOmegaMass_le_polylog
  refine ⟨C₉, hC₉, ?_⟩
  intro κ N B hN hlog hB
  let S := liuPanSquarefreeCarrier N B
  let E := liuPanActualError κ N B
  let X := liuActualEnvelopeConstant κ * N * (1 + Real.log N) ^ 2
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity [liuActualEnvelopeConstant_pos κ]
  have hsq : ∀ q ∈ S, Squarefree q := fun q hq => (mem_filter.mp hq).2
  have hpos : ∀ q ∈ S, 0 < q := by
    intro q hq
    exact Nat.pos_of_ne_zero (hsq q hq).ne_zero
  have hE : ∀ q ∈ S, 0 ≤ E q := fun q _ => liuPanActualError_nonneg κ N B q
  have henv : ∀ q ∈ S, (q : ℝ) * E q ≤ X := by
    intro q hq
    exact modulus_mul_liuMainPanCoprimeIntervalMaxL_le κ N _ _ q hN (hpos q hq)
      (panSourceStrictModulusCutoff_mem_le (by omega) hlog hB (mem_filter.mp hq).1)
  -- Finite Cauchy squares the 3^ω weight; its moment is the 9^ω mass.
  have hCauchy := Richert1969.weightedError_sq_le_lemma3Mass_mul_ordinary S
    (fun q => (3 : ℝ) ^ q.primeFactors.card) E X hpos hE henv
  have hweightMoment : (∑ q ∈ S, ((3 : ℝ) ^ q.primeFactors.card) ^ 2 / q) =
      Richert1969.lemma3NineOmegaMass S := by
    unfold Richert1969.lemma3NineOmegaMass
    apply sum_congr rfl
    intro q _
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hweightMoment] at hCauchy
  -- Nonnegativity lets us enlarge the squarefree error sum to the full unweighted sum.
  have hordinary : X * (∑ q ∈ S, E q) ≤ X * liuPanUnweightedTheorem2Sum κ N B :=
    mul_le_mul_of_nonneg_left (liuPanSquarefreeErrorSum_le_unweighted κ N B) hX
  have hmomentFactor_nonneg : 0 ≤ C₉ * Real.log (N + 2) ^ (9 : ℝ) := by
    have hlog_nonneg : 0 ≤ Real.log (N + 2) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
    exact mul_nonneg hC₉.le (Real.rpow_nonneg hlog_nonneg _)
  rw [liuPanWeightedSum_eq_squarefree]
  calc
    Richert1969.threeOmegaErrorMass S E ^ 2 ≤
        Richert1969.lemma3NineOmegaMass S * (X * ∑ q ∈ S, E q) := hCauchy
    _ ≤ (C₉ * Real.log (N + 2) ^ (9 : ℝ)) * (X * ∑ q ∈ S, E q) :=
      mul_le_mul_of_nonneg_right
        (hmoment N S (liuPanSquarefreeCarrier_subset (by omega) hlog hB) hsq)
        (mul_nonneg hX (sum_nonneg hE))
    _ ≤ _ := mul_le_mul_of_nonneg_left hordinary hmomentFactor_nonneg

end MathlibNt.SieveTheory.LiuWeight