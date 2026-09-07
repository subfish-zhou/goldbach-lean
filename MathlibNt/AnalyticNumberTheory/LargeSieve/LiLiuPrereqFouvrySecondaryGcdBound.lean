import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdCost
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonanceBound

/-!
# Refined secondary means on the original occupied fibers

All fixed-data multiplicities and the original signed weights are retained.
The new bound is no worse than the earlier dyadic mean on every occupied base.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramSecondaryGcdDyadicMean (ε C : ℝ) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (j cap : Fin 5 → ℕ) (v : WGramSecondaryBase) : ℝ :=
  wGramRCostEnvelope ε C a R S K j cap v.1 v.2.1.2.1 v.2.2.2.1
      (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1) *
    ((2 ^ (j 3 + 1) - 1 : ℕ) * Real.sqrt
      ((v.1 * v.2.2.2.1 *
        (v.2.1.2.1.gcd (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
          v.2.1.2.2).natAbs *
          (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
            v.2.1.2.2).natAbs.divisors.card) : ℕ) : ℝ))

theorem wGramSecondaryGcdDyadicMean_nonneg {C : ℝ} (hC : 0 ≤ C)
    (ε : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (v : WGramSecondaryBase) :
    0 ≤ wGramSecondaryGcdDyadicMean ε C a R S K j cap v :=
  mul_nonneg (wGramRCostEnvelope_nonneg hC ε a R S K j cap _ _ _ _ _) (by positivity)

theorem wGramSecondaryGcdDyadicMean_le_old {C : ℝ} (hC : 0 ≤ C)
    (ε : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (v : WGramSecondaryBase) (hs : 0 < v.2.1.2.1) :
    wGramSecondaryGcdDyadicMean ε C a R S K j cap v ≤
      wGramSecondaryDyadicMean ε C a R S K j cap v := by
  have hlow : 2 ^ j 3 - 1 + 1 = 2 ^ j 3 := by
    have hp : 0 < 2 ^ j 3 := by positivity
    omega
  unfold wGramSecondaryGcdDyadicMean wGramRCostEnvelope wGramSecondaryDyadicMean
  rw [hlow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact_mod_cast (show v.1 * v.2.2.2.1 *
      (v.2.1.2.1.gcd (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
        v.2.1.2.2).natAbs *
        (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
          v.2.1.2.2).natAbs.divisors.card) ≤
      v.1 * v.2.2.2.1 * v.2.1.2.1 *
        (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
          v.2.1.2.2).natAbs.divisors.card from by
    rw [mul_assoc (v.1 * v.2.2.2.1)]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.gcd_le_left _ hs)))

theorem wGramSecondaryFiber_cost_le_gcdMean
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {v : WGramSecondaryBase}
    (hv : v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))) :
    (∑ r ∈ wGramSecondaryFiber (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) v,
      wGramFouvryCost ε C a R S M Z K j cap (wGramSecondaryJoin v r)) ≤
        wGramSecondaryGcdDyadicMean ε C a R S K j cap v := by
  obtain ⟨hn, hs, hs', hsec, hl⟩ := wGramSecondaryBases_data hN hv
  calc
    _ ≤ ∑ r ∈ Ioc (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1),
        wGramFouvryCost ε C a R S M Z K j cap (wGramSecondaryJoin v r) := by
      apply sum_le_sum_of_subset_of_nonneg (wGramSecondaryFiber_subset_dyadic hN v)
      intro r _ _
      exact wGramFouvryCost_nonneg hC ε a R S M Z K j cap _
    _ ≤ _ := wGramFouvryCost_secondary_sum_refined hε hC a R S M Z K j cap
      hn hs hs' hsec hl (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1)

theorem wGramSecondaryLabels_weighted_cost_le_gcdMean
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) :
    (∑ L ∈ wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c),
      |wGramWeight K β ζ L| * wGramFouvryCost ε C a R S M Z K j cap L) ≤
    ∑ v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)),
      |wGramWeight K β ζ (wGramSecondaryJoin v 0)| *
        wGramSecondaryGcdDyadicMean ε C a R S K j cap v := by
  rw [sum_wGramSecondaryFiber_weight]
  apply sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_left (wGramSecondaryFiber_cost_le_gcdMean hε hC hN hv)
    (abs_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
