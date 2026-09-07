import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdMean

/-!
# The refined secondary mean for the actual individual-cancellation cost

Only the nonnegative span and modulus factors are replaced by endpoint
envelopes. The arithmetic square-root sum is still averaged in `r`.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramRCostEnvelope (ε C : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (n s s' lo hi : ℕ) : ℝ :=
  C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (n * (lo + 1) * s * s' : ℕ)) *
    (n * hi * s * s' : ℕ) ^ (1 / 2 + ε : ℝ)

theorem wGramRCostEnvelope_nonneg {C : ℝ} (hC : 0 ≤ C)
    (ε : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (n s s' lo hi : ℕ) :
    0 ≤ wGramRCostEnvelope ε C a R S K j cap n s s' lo hi := by
  unfold wGramRCostEnvelope
  positivity

theorem wGramFouvryCost_le_rEnvelope
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ)
    {n n₂ n₂' s s' r lo hi : ℕ} {h h' : ℤ}
    (hn : 0 < n) (hs : 0 < s) (hs' : 0 < s') (hr : r ∈ Ioc lo hi) :
    wGramFouvryCost ε C a R S M Z K j cap ((r, n), (n₂, s, h), (n₂', s', h')) ≤
      wGramRCostEnvelope ε C a R S K j cap n s s' lo hi *
        Real.sqrt ((n * r * s * s').gcd
          (iv3CorrelationNumerator K.1.2.1 n n₂ n₂' s s' a h h').natAbs : ℝ) := by
  have hqlo : 0 < (n * (lo + 1) * s * s' : ℝ) := by positivity
  have hqr : (n * (lo + 1) * s * s' : ℝ) ≤ (n * r * s * s' : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right s' (Nat.mul_le_mul_right s
      (Nat.mul_le_mul_left n (mem_Ioc.mp hr).1))
  have hqhi : (n * r * s * s' : ℝ) ≤ (n * hi * s * s' : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right s' (Nat.mul_le_mul_right s
      (Nat.mul_le_mul_left n (mem_Ioc.mp hr).2))
  have hspan : (wGramSpan R S M Z K j cap
      ((r, n), (n₂, s, h), (n₂', s', h')) : ℝ) ≤
      (wKSectionGridUpper R S K j cap + 1 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ _) 1
  have hd := div_le_div₀ (by positivity) hspan hqlo hqr
  have hp := Real.rpow_le_rpow (by positivity) hqhi (by linarith : 0 ≤ 1 / 2 + ε)
  change C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + (wGramSpan R S M Z K j cap
      ((r, n), (n₂, s, h), (n₂', s', h')) : ℝ) / (n * r * s * s' : ℕ)) *
    Real.sqrt _ * (n * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) ≤ _
  unfold wGramRCostEnvelope
  push_cast at hd hp ⊢
  calc
    _ = (C * (a.natAbs.divisors.card : ℝ) *
        ((K.D' : ℝ) + (wGramSpan R S M Z K j cap
          ((r, n), (n₂, s, h), (n₂', s', h')) : ℝ) / (n * r * s * s')) *
        (n * r * s * s') ^ (1 / 2 + ε : ℝ)) * Real.sqrt _ := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hd) (by positivity))
        hp (by positivity) (by positivity)

theorem wGramFouvryCost_secondary_sum_refined
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ)
    {n n₂ n₂' s s' : ℕ} {h h' : ℤ}
    (hn : 0 < n) (hs : 0 < s) (hs' : 0 < s')
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator K.1.2.1 n n₂ n₂' s s' a h h' ≠ 0)
    (lo hi : ℕ) :
    (∑ r ∈ Ioc lo hi, wGramFouvryCost ε C a R S M Z K j cap
      ((r, n), (n₂, s, h), (n₂', s', h'))) ≤
      wGramRCostEnvelope ε C a R S K j cap n s s' lo hi *
        (hi * Real.sqrt ((n * s' *
          (s.gcd (iv3SecondaryNumerator K.1.2.1 n₂ n₂' a h).natAbs *
            (iv3SecondaryNumerator K.1.2.1 n₂ n₂' a h).natAbs.divisors.card) : ℕ) : ℝ)) := by
  let E := wGramRCostEnvelope ε C a R S K j cap n s s' lo hi
  let f := fun r => Real.sqrt ((n * r * s * s').gcd
    (iv3CorrelationNumerator K.1.2.1 n n₂ n₂' s s' a h h').natAbs : ℝ)
  have hE : 0 ≤ E := wGramRCostEnvelope_nonneg hC ε a R S K j cap n s s' lo hi
  calc
    _ ≤ ∑ r ∈ Ioc lo hi, E * f r :=
      sum_le_sum (fun _ hr => wGramFouvryCost_le_rEnvelope
        hε hC a R S M Z K j cap hn hs hs' hr)
    _ = E * ∑ r ∈ Ioc lo hi, f r := (mul_sum _ _ _).symm
    _ ≤ E * ∑ r ∈ Ioc 0 hi, f r := by
      apply mul_le_mul_of_nonneg_left _ hE
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le lo) (mem_Ioc.mp hr).1,
          (mem_Ioc.mp hr).2⟩
      · intro r _ _
        exact Real.sqrt_nonneg _
    _ ≤ _ := mul_le_mul_of_nonneg_left (iv3_secondary_sqrt_gcd_sum_refined hsec hl hi) hE

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
