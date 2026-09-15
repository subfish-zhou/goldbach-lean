import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Quantitative lower profile in Proposition 13.1(ii), κ = 1. -/
noncomputable def proposition131iiLowerProfile (C s : ℝ) : ℝ :=
  Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) - C * s)

/-- Uniform two-sign quantitative lower form of Proposition 13.1(ii). -/
def Proposition131iiUniformQuantitativeLower (H : Section13HatLayers) : Prop :=
  ∃ C M : ℝ, 0 ≤ C ∧ 3 ≤ M ∧
    ∀ (sign : ErrorSign) (s : ℝ), M ≤ s →
      proposition131iiLowerProfile C s ≤ H.T sign s

/-- The first, fully internal step of the lower-bound argument: the source DDE
and `weightedHat → 0` give the exact positive tail representation. -/
theorem proposition131ii_source_tail_identity
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s : ℝ} (hs : 3 < s) :
    (∫ t in Ioi s, hatTailIntegrand H sign t) = weightedHat H sign s := by
  exact integral_Ioi_hatTailIntegrand hH.toSection13HatContract sign (by
    cases sign <;> simp [ErrorSign.epsilon] at hs ⊢ <;> linarith)

/-- Every first unit of the tail has mass strictly smaller than the whole tail.
This is the positivity input used by the source unit-interval iteration. -/
theorem proposition131ii_first_unit_strict
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s : ℝ} (hs : 3 < s) :
    (∫ t in s..s + 1, hatTailIntegrand H sign t) < weightedHat H sign s := by
  have hfinite := integral_hatTailIntegrand hH.toSection13HatContract sign (by
    cases sign <;> simp [ErrorSign.epsilon] at hs ⊢ <;> linarith) (by linarith : s ≤ s + 1)
  rw [hfinite]
  have hwpos : 0 < weightedHat H sign (s + 1) := by
    exact mul_pos (sq_pos_of_pos (by linarith)) (hH.positive sign (s + 1) (by linarith))
  linarith

/-- Pointwise kernel estimate on the first unit.  Together with the preceding
strict mass inequality it is the first nontrivial ratio produced by the
unit-interval argument, without assuming any lower or asymptotic estimate. -/
theorem proposition131ii_first_unit_pointwise
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s t : ℝ} (hs : 4 < s) (ht : t ∈ Icc s (s + 1)) :
    (1 / s) * weightedHat H sign.opposite s ≤ hatTailIntegrand H sign t := by
  rcases ht with ⟨hst, hts⟩
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have htm1 : 0 < t - 1 := by linarith
  have hanti : weightedHat H sign.opposite s ≤ weightedHat H sign.opposite (t - 1) := by
    have hmono := weightedHat_antitoneOn_Icc hH.toSection13HatContract sign.opposite
      (a := s - 1) (b := s) (by
        cases sign <;> simp [ErrorSign.opposite, ErrorSign.epsilon] at hs ⊢ <;> linarith)
    apply hmono
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩
    · linarith
  have hw0 : 0 ≤ weightedHat H sign.opposite (t - 1) := by
    exact (mul_pos (sq_pos_of_pos htm1)
      (hH.positive sign.opposite (t - 1) htm1)).le
  have hk : 1 / s ≤ t / (t - 1) ^ 2 := by
    rw [div_le_div_iff₀ hs0 (sq_pos_of_pos htm1)]
    nlinarith [mul_nonneg ht0.le (by linarith : 0 ≤ s + 1 - t)]
  calc
    (1 / s) * weightedHat H sign.opposite s ≤
        (1 / s) * weightedHat H sign.opposite (t - 1) := by
      exact mul_le_mul_of_nonneg_left hanti (by positivity)
    _ ≤ (t / (t - 1) ^ 2) * weightedHat H sign.opposite (t - 1) := by
      exact mul_le_mul_of_nonneg_right hk hw0
    _ = hatTailIntegrand H sign t := by
      simp only [weightedHat, hatTailIntegrand]
      field_simp [ne_of_gt htm1]

/-- The resulting honest one-unit ratio edge.  It is strictly weaker than the
factorial iteration needed for Proposition 13.1(ii), but is derived solely from
the source contract and identifies the exact starting inequality for that
iteration. -/
theorem proposition131ii_first_unit_ratio
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s : ℝ} (hs : 4 < s) :
    (1 / s) * weightedHat H sign.opposite s < weightedHat H sign s := by
  have hcont : ContinuousOn (hatTailIntegrand H sign) (Icc s (s + 1)) := by
    apply continuousOn_id.mul
    apply (hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const)
    intro t ht
    exact (by linarith [ht.1] : 0 < t - 1)
  have hmono :
      (∫ t in s..s + 1, (1 / s) * weightedHat H sign.opposite s) ≤
        ∫ t in s..s + 1, hatTailIntegrand H sign t := by
    apply intervalIntegral.integral_mono_on (by linarith : s ≤ s + 1)
    · exact intervalIntegrable_const
    · exact hcont.intervalIntegrable_of_Icc (by linarith : s ≤ s + 1)
    · intro t ht
      exact proposition131ii_first_unit_pointwise hH sign hs ht
  have hconst :
      (∫ _t in s..s + 1, (1 / s) * weightedHat H sign.opposite s) =
        (1 / s) * weightedHat H sign.opposite s := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hconst] at hmono
  exact hmono.trans_lt (proposition131ii_first_unit_strict hH sign (by linarith))


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
