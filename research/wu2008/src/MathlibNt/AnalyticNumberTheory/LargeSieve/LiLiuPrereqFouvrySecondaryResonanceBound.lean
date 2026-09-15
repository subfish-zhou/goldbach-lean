import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonanceReindex

/-!
# Consuming the secondary r-mean on the original occupied carrier

Only nonnegative costs are enlarged to the actual dyadic `r` interval.
The signed coefficient weight remains an exact, `r`-independent factor.
The mean keeps the existing losses: the span is bounded by `GridUpper+1`,
and the gcd average extends to `(0,hi]`, rather than paying just the width.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wGramFouvryCost_nonneg {C : ℝ} (hC : 0 ≤ C)
    (ε : ℝ) (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (L : WGramLabel) :
    0 ≤ wGramFouvryCost ε C a R S M Z K j cap L := by
  unfold wGramFouvryCost
  positivity

/-- Explicit dyadic mean for a fixed seven-coordinate base. The lower
modulus uses `2^(j 3)` and the averaging cost uses `2^(j 3+1)-1`. -/
def wGramSecondaryDyadicMean (ε C : ℝ) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (j cap : Fin 5 → ℕ) (v : WGramSecondaryBase) : ℝ :=
  (C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (v.1 * 2 ^ j 3 * v.2.1.2.1 * v.2.2.2.1 : ℕ)) *
    (v.1 * (2 ^ (j 3 + 1) - 1) * v.2.1.2.1 * v.2.2.2.1 : ℕ) ^
      (1 / 2 + ε : ℝ)) *
  ((2 ^ (j 3 + 1) - 1 : ℕ) * Real.sqrt
    ((v.1 * v.2.2.2.1 * v.2.1.2.1 *
      (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
        v.2.1.2.2).natAbs.divisors.card : ℕ) : ℝ))

theorem wGramSecondaryDyadicMean_nonneg {C : ℝ} (hC : 0 ≤ C)
    (ε : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (v : WGramSecondaryBase) :
    0 ≤ wGramSecondaryDyadicMean ε C a R S K j cap v := by
  unfold wGramSecondaryDyadicMean
  positivity

/-- Eligibility comes from an occupied label. No positivity or nonzero
coefficient is imposed on unoccupied bases, and no mean in `n` is used. -/
theorem wGramSecondaryFiber_cost_le_mean
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
        wGramSecondaryDyadicMean ε C a R S K j cap v := by
  obtain ⟨hn, hs, hs', hsec, hl⟩ := wGramSecondaryBases_data hN hv
  have hlow : 2 ^ j 3 - 1 + 1 = 2 ^ j 3 := by
    have hp : 0 < 2 ^ j 3 := by positivity
    omega
  calc
    _ ≤ ∑ r ∈ Ioc (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1),
        wGramFouvryCost ε C a R S M Z K j cap (wGramSecondaryJoin v r) := by
      apply sum_le_sum_of_subset_of_nonneg (wGramSecondaryFiber_subset_dyadic hN v)
      intro r _ _
      exact wGramFouvryCost_nonneg hC ε a R S M Z K j cap _
    _ ≤ _ := by
      simpa only [wGramSecondaryJoin, wGramSecondaryDyadicMean, hlow] using
        wGramFouvryCost_secondary_sum hε hC a R S M Z K j cap hn hs hs' hsec hl
          (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1)

/-- The original secondary aggregate is replaced by a proved mean. Every
remaining fixed-data multiplicity and the exact absolute signed weight remain
visible in the outer sum; this is not a globally normalized C.2 estimate. -/
theorem wGramSecondaryLabels_weighted_cost_le
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
        wGramSecondaryDyadicMean ε C a R S K j cap v := by
  rw [sum_wGramSecondaryFiber_weight]
  apply sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_left (wGramSecondaryFiber_cost_le_mean hε hC hN hv)
    (abs_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
