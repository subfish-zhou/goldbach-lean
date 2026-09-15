import FifthHIntegral
import MathlibNt.Wu2008DoubleSieve.PhiEndpoint
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

/-- Same ordered labels and full cofactor; only the sifting cutoff is closed. -/
noncomputable def fifthHClosedCount (N : ℕ) : ℤ :=
  ∑ q ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
    ((N : ℝ) ^ truncatedSixthLowerBeta),
    ∑ p ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha) (q : ℝ),
      sieveCountLE N (p * q) N ((N : ℝ) ^ truncatedSixthLowerAlpha)

noncomputable def fifthHEndpointLoss (N : ℕ) : ℝ :=
  ∑ t ∈ fifthPairLabels N,
    ((sieveEndpointLoss N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha)).card : ℝ)

theorem fifthH_closed_count_eq (N : ℕ) :
    (fifthHClosedCount N : ℝ) = ∑ t ∈ fifthPairLabels N,
      (sieveCountLE N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  rw [fifthPair_sum_eq]
  simp only [fifthHClosedCount, Int.cast_sum]

theorem fifthH_strict_eq_closed_add_loss (N : ℕ) :
    (fifthPairCount N : ℝ) = (fifthHClosedCount N : ℝ) + fifthHEndpointLoss N := by
  rw [fifthPair_count_eq, fifthH_closed_count_eq]
  unfold fifthHEndpointLoss
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  exact_mod_cast sieveCount_eq_closed_add_loss N (t.1 * t.2) N
    ((N : ℝ) ^ truncatedSixthLowerAlpha)

/-- The genuine endpoint injection retains the full selected divisor in the denominator. -/
theorem fifthH_endpoint_loss_le {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    fifthHEndpointLoss N ≤ (N : ℝ) / (N : ℝ) ^ truncatedSixthLowerAlpha *
      (truncatedSixthMassPrimeSum N truncatedSixthLowerAlpha truncatedSixthLowerBeta) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (N : ℝ) ^ truncatedSixthLowerAlpha := rpow_pos_of_pos hNR _
  calc
    _ ≤ ∑ t ∈ fifthPairLabels N,
        (N : ℝ) / ((t.1 * t.2 : ℕ) * (N : ℝ) ^ truncatedSixthLowerAlpha) := by
      apply sum_le_sum
      intro t ht
      obtain ⟨ha, hb⟩ := mem_product.mp (mem_filter.mp ht).1
      exact sieveEndpointLoss_card_le_divisor hN he
        (mul_pos (mem_primeWindow.mp ha).1.pos (mem_primeWindow.mp hb).1.pos) hp
    _ = (N : ℝ) / (N : ℝ) ^ truncatedSixthLowerAlpha *
        ∑ t ∈ fifthPairLabels N, 1 / ((t.1 : ℝ) * t.2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t _
      rw [Nat.cast_mul]
      ring
    _ ≤ (N : ℝ) / (N : ℝ) ^ truncatedSixthLowerAlpha *
        ∑ t ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
          ((N : ℝ) ^ truncatedSixthLowerBeta) ×ˢ
          primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
            ((N : ℝ) ^ truncatedSixthLowerBeta), 1 / ((t.1 : ℝ) * t.2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by
      rw [pow_two]
      congr 1
      simp only [truncatedSixthMassPrimeSum, sum_product, sum_mul, mul_sum,
        one_div_mul_one_div]
      exact sum_comm

/-- Fixed endpoint losses are paid independently of delta and the mesh resolution. -/
theorem fifthH_endpoint_relative {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      fifthHEndpointLoss N ≤ ε * truncatedSixthMassScale N := by
  let K := log (truncatedSixthLowerBeta / truncatedSixthLowerAlpha) ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hlim := (truncatedSixthMass_prime_tendsto truncatedSixthLower_parameters.1
    truncatedSixthLower_parameters.2.1.le).pow 2
  have hm := hlim.eventually (gt_mem_nhds (show
    log (truncatedSixthLowerBeta / truncatedSixthLowerAlpha) ^ 2 < K by dsimp [K]; linarith))
  have hbudget := box_eventually_log_power_budget 2
    (show 0 < K / (ε * liuUniversalProduct) from div_pos hK (mul_pos hε liuUniversalProduct_pos))
    truncatedSixthLower_parameters.1
  filter_upwards [hm, hbudget, eventually_ge_atTop (4 : ℕ)] with N hm hb hN he
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hU : liuUniversalProduct ≤ wuSingularSeries N := by
    rw [wuSingularSeries_eq_liu _ (by omega)]
    exact liuUniversalProduct_le_liuSingularSeries _
  calc
    _ ≤ (N : ℝ) / (N : ℝ) ^ truncatedSixthLowerAlpha * K :=
      (fifthH_endpoint_loss_le hN he).trans
        (mul_le_mul_of_nonneg_left hm.le (by positivity))
    _ ≤ (N : ℝ) / ((K / (ε * liuUniversalProduct)) * log N ^ 2) * K :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hNR.le
        (mul_pos (div_pos hK (mul_pos hε liuUniversalProduct_pos)) (pow_pos hl 2)) hb) hK.le
    _ = ε * (liuUniversalProduct * N / log N ^ 2) := by field_simp
    _ ≤ ε * truncatedSixthMassScale N := by
      unfold truncatedSixthMassScale
      gcongr

/-- Entire original triangular actual h integral, now at the printed closed cutoff. -/
theorem fifthH_actual_closed_Fdelta_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthHFdelta δ - ε) * truncatedSixthMassScale N ≤ (fifthHClosedCount N : ℝ) := by
  obtain ⟨T1, hT14, hstrict⟩ := fifthH_actual_Fdelta_lower hδ hδhi (half_pos hε)
  obtain ⟨T2, hclosed⟩ := eventually_atTop.mp (fifthH_endpoint_relative (half_pos hε))
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hs := hstrict N ((le_max_left _ _).trans hN) he
  have hc := hclosed N ((le_max_right _ _).trans hN) he
  rw [fifthH_strict_eq_closed_add_loss] at hs
  nlinarith

end Wu2008DoubleSieve
