import MathlibNt.Wu2008DoubleSieve.ClosedLowerWeightEndpoints

/-!
# A closed-quotient variant of Wu (2008), Lemma 2.1

All sieve terms use `q ≤ z`; all prime summation ranges remain exactly
those of `lowerWeightRHS`. The change of convention is paid explicitly:
single endpoint losses cost at most `κ⁻¹ N^(1-κ)`, and weighted pair
endpoint losses cost at most `4 κ⁻² N^(1-κ)`. Positive terms only decrease.
These are quotient-sequence counts. Wu04 defines `A_d` as an unscaled
divisible subsequence, so this is not the literal printed closed/unscaled
formula: at a selected prime endpoint those carriers can differ even on
squarefree complements.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def closedLowerS2 (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => w ≤ (t.1 : ℝ)),
    sieveCountLE N (t.1 * t.2) (N * t.1) (t.2 : ℝ)

noncomputable def closedLowerS3 (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    sieveCountLE N (t.1 * t.2) (N * t.1) (t.2 : ℝ)

/-- Literal `2S - S₁ - 2S₂ - S₃ + S₄`, with closed quotient sifting. -/
noncomputable def closedLowerWeightRHS (N : ℕ) (z w : ℝ) : ℤ :=
  2 * sieveCountLE N 1 N z -
    (∑ q ∈ primeWindow N z w, sieveCountLE N q N z) -
    2 * closedLowerS2 N z w - closedLowerS3 N z w +
    ∑ t ∈ orderedTriples (primeWindow N z w),
      sieveCountLE N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)

theorem closed_lower_pair_sum_split (N : ℕ) (z w : ℝ) :
    (∑ t ∈ lowerPairs N N z w,
      (if w ≤ (t.1 : ℝ) then 2 else 1) *
        sieveCountLE N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) =
      2 * closedLowerS2 N z w + closedLowerS3 N z w := by
  simp only [closedLowerS2, closedLowerS3, sum_filter, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases h : w ≤ (t.1 : ℝ)
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

/-- Only negative-term losses need paying; no absolute signed error estimate
or pointwise cancellation for a closed triple term is assumed. -/
theorem closedLowerWeightRHS_le_strict_add_losses (N : ℕ) (z w : ℝ) :
    closedLowerWeightRHS N z w ≤ lowerWeightRHS N z w +
      (∑ q ∈ primeWindow N z w, ((sieveEndpointLoss N q N z).card : ℤ)) +
      2 * ∑ t ∈ lowerPairs N N z w,
        ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℤ) := by
  have hs :
      (∑ q ∈ primeWindow N z w, sieveCount N q N z) =
        (∑ q ∈ primeWindow N z w, sieveCountLE N q N z) +
          ∑ q ∈ primeWindow N z w, ((sieveEndpointLoss N q N z).card : ℤ) := by
    simp only [sieveCount_eq_closed_add_loss, sum_add_distrib]
  have hp :
      2 * lowerS2 N z w + lowerS3 N z w ≤
        2 * closedLowerS2 N z w + closedLowerS3 N z w +
          2 * ∑ t ∈ lowerPairs N N z w,
            ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℤ) := by
    rw [← lower_pair_sum_split, ← closed_lower_pair_sum_split, mul_sum,
      ← sum_add_distrib]
    apply sum_le_sum
    intro t _
    rw [sieveCount_eq_closed_add_loss]
    split_ifs <;> omega
  have hb := sieveCountLE_le_strict N 1 N z
  have ht :
      (∑ t ∈ orderedTriples (primeWindow N z w),
        sieveCountLE N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)) ≤
      ∑ t ∈ orderedTriples (primeWindow N z w),
        sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) :=
    sum_le_sum (fun t _ => sieveCountLE_le_strict N
      (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ))
  unfold closedLowerWeightRHS lowerWeightRHS
  omega

theorem closedLowerWeightRHS_le_strict_add_paid_error {N : ℕ}
    (hN : 4 ≤ N) (he : Even N) {κ w : ℝ} (hκ : 0 < κ)
    (hz : 2 ≤ (N : ℝ) ^ κ) (hzw : (N : ℝ) ^ κ ≤ w) :
    (closedLowerWeightRHS N ((N : ℝ) ^ κ) w : ℝ) ≤
      (lowerWeightRHS N ((N : ℝ) ^ κ) w : ℝ) +
        (1 / κ + 4 * (1 / κ) ^ 2) * (N : ℝ) ^ (1 - κ) := by
  have hc := closedLowerWeightRHS_le_strict_add_losses N ((N : ℝ) ^ κ) w
  have hc' :
      (closedLowerWeightRHS N ((N : ℝ) ^ κ) w : ℝ) ≤
        (lowerWeightRHS N ((N : ℝ) ^ κ) w : ℝ) +
          (∑ q ∈ primeWindow N ((N : ℝ) ^ κ) w,
            ((sieveEndpointLoss N q N ((N : ℝ) ^ κ)).card : ℝ)) +
          2 * ∑ t ∈ lowerPairs N N ((N : ℝ) ^ κ) w,
            ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℝ) := by
    exact_mod_cast hc
  have hs := single_endpoint_sum_le hN he hκ w
  have hp := pair_endpoint_sum_le hN he hκ hz hzw
  have hpow : (N : ℝ) / (N : ℝ) ^ κ = (N : ℝ) ^ (1 - κ) := by
    rw [Real.rpow_sub (by positivity : (0 : ℝ) < N), Real.rpow_one]
  rw [hpow] at hs hp
  nlinarith

/-- A closed-quotient variant of Wu08 (2.1), with a genuine explicit
`O_κ(N^(1-κ))` payment. The endpoint `σ = 1/3` is retained, and there is no
`3σ + κ > 1` hypothesis. Units remain in the actual `Ω ≤ 2` carrier. -/
theorem wu_lemma21_closed {κ σ : ℝ}
    (hκ : 0 < κ) (hκσ : κ < σ) (hσ : σ ≤ 1 / 3) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      (closedLowerWeightRHS N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) : ℝ) -
        (8 + 1 / κ + 4 * (1 / κ) ^ 2) * (N : ℝ) ^ (1 - κ) ≤
          2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨N1, hstrict⟩ := wu_lemma21_strict hκ hκσ hσ
  have hz : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ (N : ℝ) ^ κ :=
    ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 2)
  apply Filter.eventually_atTop.mp
  filter_upwards [hz, Filter.eventually_ge_atTop (max N1 4)] with N hzN hN
  intro he
  have hN4 : 4 ≤ N := (le_max_right N1 4).trans hN
  have hNN1 : N1 ≤ N := (le_max_left N1 4).trans hN
  have hs := hstrict N hNN1
  have hzw : (N : ℝ) ^ κ ≤ (N : ℝ) ^ σ :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hκσ.le
  have hc := closedLowerWeightRHS_le_strict_add_paid_error hN4 he hκ hzN hzw
  nlinarith

end Wu2008DoubleSieve
