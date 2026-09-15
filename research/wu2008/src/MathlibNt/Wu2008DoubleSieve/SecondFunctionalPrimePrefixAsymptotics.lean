import MathlibNt.Wu2008DoubleSieve.NinthMainMassPNT

/-! # Actual finite prime prefixes above a moving power threshold
The existing two-sided PNT envelope is reused, not assumed by callers.
All real prefix endpoints follow the common threshold. -/
namespace Wu2008DoubleSieve
open Finset Set Filter Real LiLiuPrereqBuchstab
open scoped Classical Topology

/-- The real-endpoint prime counting function is the actual closed finite prefix. -/
theorem secondFunctional_primePrefix_card {z : ℝ} (hz : 0 ≤ z) :
    ((primesIcc 0 z).card : ℝ) = primePi z := by
  have hs : primesIcc 0 z = (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime := by
    ext p
    simp [mem_primesIcc hz, Nat.le_floor_iff hz, and_comm]
  rw [hs, primePi_eq_sum_indicator]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- A fixed positive exponent precedes the threshold; z is not fixed in advance. -/
theorem secondFunctional_primePrefix_eventually (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ z : ℝ, R ^ a ≤ z →
      |((primesIcc 0 z).card : ℝ) - z / log z| ≤ ε * (z / log z) := by
  filter_upwards [(tendsto_rpow_atTop ha).eventually (eventually_ge_atTop primeErrorStart),
    (tendsto_primeErrorEnvelope.comp (tendsto_rpow_atTop ha)).eventually
      (gt_mem_nhds hε)] with R hs he
  intro z hz
  have hz1 : 1 < z := by linarith [primeErrorStart_spec.1]
  rw [secondFunctional_primePrefix_card (by linarith)]
  exact (primePi_error_le hs hz).trans
    (mul_le_mul_of_nonneg_right he.le (div_nonneg (by linarith) (log_pos hz1).le))

/-- The full two-sided finite-prefix estimate, uniformly over all later real endpoints. -/
theorem secondFunctional_primePrefix_threshold (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∀ z : ℝ, R ^ a ≤ z →
      |((primesIcc 0 z).card : ℝ) - z / log z| ≤ ε * (z / log z) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (secondFunctional_primePrefix_eventually a ha ε hε)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro R hR
  exact hT R ((le_max_left _ _).trans hR)

/-- Literal power-endpoint consumer for both ends of the later clipped prime fibre. -/
theorem secondFunctional_primePrefix_power_threshold (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∀ t : ℝ, a ≤ t →
      |((primesIcc 0 (R ^ t)).card : ℝ) - R ^ t / (t * log R)| ≤
        ε * (R ^ t / (t * log R)) := by
  obtain ⟨T,hT1,hT⟩ := secondFunctional_primePrefix_threshold a ha ε hε
  refine ⟨T,hT1,?_⟩
  intro R hR t ht
  have hR1 : 1 < R := hT1.trans_le hR
  have hp := hT R hR (R ^ t) (rpow_le_rpow_of_exponent_le hR1.le ht)
  simpa only [log_rpow (show 0 < R by linarith)] using hp

end Wu2008DoubleSieve
