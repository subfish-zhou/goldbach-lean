import Hf4OuterDensity

noncomputable section
namespace Hf4Outer
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open SigmaVariableOuterPayment
open scoped Interval BigOperators

/-- A literal rational endpoint difference on the original cell, not an integral definition. -/
def cellPayment (a b : ℝ) : ℝ :=
  ((b-1)^9-(a-1)^9)/(3024*b*(b+5)^3*(b+11)^4)

theorem cellDensity_integral (a : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ t in a..b, cellDensity b t) = cellPayment a b := by
  have hb0 : b ≠ 0 := by linarith
  have h5 : b+5 ≠ 0 := by linarith
  have h11 : b+11 ≠ 0 := by linarith
  have hd (t : ℝ) : HasDerivAt
      (fun u : ℝ => (u-1)^9/(3024*b*(b+5)^3*(b+11)^4)) (cellDensity b t) t := by
    convert (((hasDerivAt_id t).sub_const 1).pow 9).div_const
      (3024*b*(b+5)^3*(b+11)^4) using 1 <;>
      first | rfl | (dsimp [cellDensity]; field_simp; ring)
  have hi : IntervalIntegrable (cellDensity b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold cellDensity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  unfold cellPayment
  ring

theorem cellPayment_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ cellPayment a b := by
  rw [← cellDensity_integral a (ha.trans hab)]
  apply intervalIntegral.integral_nonneg hab
  intro t _
  have hb0 : 0 < b := by linarith
  unfold cellDensity
  positivity

theorem cellPayment_pos {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    0 < cellPayment a b := by
  rw [← cellDensity_integral a (ha.trans hab.le)]
  have hi : IntervalIntegrable (cellDensity b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold cellDensity
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hi _ hab
  intro t ht
  have hb0 : 0 < b := by linarith
  have ht1 : 0 < t-1 := by linarith [ht.1]
  unfold cellDensity
  positivity

theorem cellPayment_le_loss {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    cellPayment a b ≤ SigmaVariableFull.cellMass a b-rationalCellMass a b := by
  have hsub : uIcc a b ⊆ uIcc (1:ℝ) 3 := by
    rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    exact fun t ht => ⟨ha.trans ht.1,ht.2.trans hb⟩
  have hi : IntervalIntegrable SigmaVariableFull.weight volume a b :=
    (SigmaVariableFull.weight_continuous.mono hsub).intervalIntegrable
  have hj : IntervalIntegrable paidWeight volume a b :=
    (paidWeight_continuous.mono hsub).intervalIntegrable
  have hk : IntervalIntegrable (cellDensity b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold cellDensity
    fun_prop
  rw [← cellDensity_integral a (ha.trans hab)]
  unfold SigmaVariableFull.cellMass rationalCellMass
  rw [← intervalIntegral.integral_sub hi hj]
  apply intervalIntegral.integral_mono_on hab hk (hi.sub hj)
  exact fun t ht => cellDensity_le_loss ⟨ha.trans ht.1,ht.2.trans hb⟩ ht.2

/-- Endpoint freezing still leaves positive loss throughout every original cell interior. -/
theorem cellDensity_lt_loss {t b : ℝ} (ht : 1 < t) (htb : t < b) (hb : b ≤ 3) :
    cellDensity b t < SigmaVariableFull.weight t-paidWeight t := by
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < b := by linarith
  have hlt : cellDensity b t < outerDensity t := by
    unfold cellDensity outerDensity
    apply div_lt_div_of_pos_left (pow_pos (sub_pos.mpr ht) 8) (by positivity)
    gcongr
  exact hlt.trans_le (outerDensity_le_loss ⟨ht.le,htb.le.trans hb⟩)

theorem cellPayment_lt_loss {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 3) :
    cellPayment a b < SigmaVariableFull.cellMass a b-rationalCellMass a b := by
  have hsub : uIcc a b ⊆ uIcc (1:ℝ) 3 := by
    rw [uIcc_of_le hab.le,uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    exact fun t ht => ⟨ha.trans ht.1,ht.2.trans hb⟩
  have hi : IntervalIntegrable SigmaVariableFull.weight volume a b :=
    (SigmaVariableFull.weight_continuous.mono hsub).intervalIntegrable
  have hj : IntervalIntegrable paidWeight volume a b :=
    (paidWeight_continuous.mono hsub).intervalIntegrable
  have hk : IntervalIntegrable (cellDensity b) volume a b := by
    apply Continuous.intervalIntegrable
    unfold cellDensity
    fun_prop
  have hp : 0 < ∫ t in a..b,
      (SigmaVariableFull.weight t-paidWeight t)-cellDensity b t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on ((hi.sub hj).sub hk)
      (fun t ht => sub_pos.mpr (cellDensity_lt_loss (ha.trans_lt ht.1) ht.2 hb)) hab
  rw [intervalIntegral.integral_sub (hi.sub hj) hk,intervalIntegral.integral_sub hi hj,
    cellDensity_integral a (ha.trans hab.le)] at hp
  exact sub_pos.mp hp

/-- Finite sum of explicit rational original-cell payments; original H is untouched. -/
def payment : ℝ := ∑ k : Fin 9, NineFeedbackStrength.originalH k *
  cellPayment (upperLeft k) (upperNode k)

theorem payment_pos : 0 < payment := by
  apply Finset.sum_pos'
  · intro k _
    obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_nonneg (CoupledIntegralRecovery.originalH_nonneg k) (cellPayment_nonneg ha hab)
  · obtain ⟨k,hk⟩ := Hf4Next.original_has_positive_weight
    exact ⟨k,Finset.mem_univ k,mul_pos hk
      (cellPayment_pos (SigmaEndpointPayment.original_cell_bounds k).1
        (Hf4Next.original_cell_strict k))⟩

theorem payment_le_outerUnpaid : payment ≤ Hf4Full.outerUnpaid := by
  unfold Hf4Full.outerUnpaid
  rw [SigmaActualBlockSeparable.endpointNumerator_eq_rational]
  simp only [SigmaVariableFull.numerator,rationalNumerator,← Finset.sum_sub_distrib,← mul_sub]
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
  exact mul_le_mul_of_nonneg_left (cellPayment_le_loss ha hab hb)
    (CoupledIntegralRecovery.originalH_nonneg k)

theorem payment_lt_outerUnpaid : payment < Hf4Full.outerUnpaid := by
  unfold Hf4Full.outerUnpaid
  rw [SigmaActualBlockSeparable.endpointNumerator_eq_rational]
  simp only [SigmaVariableFull.numerator,rationalNumerator,← Finset.sum_sub_distrib,← mul_sub]
  apply Finset.sum_lt_sum
  · intro k _
    obtain ⟨ha,hab,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_le_mul_of_nonneg_left (cellPayment_le_loss ha hab hb)
      (CoupledIntegralRecovery.originalH_nonneg k)
  · obtain ⟨k,hk⟩ := Hf4Next.original_has_positive_weight
    obtain ⟨ha,_,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact ⟨k,Finset.mem_univ k,mul_lt_mul_of_pos_left
      (cellPayment_lt_loss ha (Hf4Next.original_cell_strict k) hb) hk⟩

end Hf4Outer
