import SrcFourLowerProfile

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFour

theorem weightFloor_bounds : 0 < weightFloor ∧ weightFloor ≤ 8 := by
  norm_num [weightFloor,alpha,truncatedSixthLowerAlpha]

theorem original_weight_floor :
    weightFloor*(∫ x in alpha..beta, regularOuter10 x+regularOuter11 x) ≤
      original10+original11 := by
  have hac := geometry.1.le
  have hcb := geometry.2.1.le.trans geometry.2.2.1.le
  have ho : Continuous (fun x => regularOuter10 x+regularOuter11 x) :=
    regularOuter10_continuous.add regularOuter11_continuous
  have hs := ho.intervalIntegrable (μ := volume) alpha (1/10 : ℝ)
  have hl := ho.intervalIntegrable (μ := volume) (1/10 : ℝ) beta
  have hw := weighted_integrable ho
  have hmono := intervalIntegral.integral_mono_on hac (hs.const_mul weightFloor)
    (hw.const_mul (36/5)) (fun x hx => by
      have hO : 0 ≤ regularOuter10 x+regularOuter11 x :=
        add_nonneg (outer10_nonneg ⟨hx.1,hx.2.trans hcb⟩)
          (outer11_nonneg ⟨hx.1,hx.2.trans hcb⟩)
      have hden : 0 < 1-x := by linarith only [hx.2]
      have hd : 0 < 1-alpha := by linarith only [hx.1,hden]
      have he : weightFloor ≤ (36/5)/(1-x) := by
        unfold weightFloor
        exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith only [hx.1])
      convert mul_le_mul_of_nonneg_right he hO using 1 <;> first | rfl | ring)
  have hlarge0 : 0 ≤ ∫ x in (1/10 : ℝ)..beta, regularOuter10 x+regularOuter11 x :=
    intervalIntegral.integral_nonneg hcb (fun x hx =>
      add_nonneg (outer10_nonneg ⟨hac.trans hx.1,hx.2⟩)
        (outer11_nonneg ⟨hac.trans hx.1,hx.2⟩))
  have hlarge := mul_le_mul_of_nonneg_right weightFloor_bounds.2 hlarge0
  have hadj := intervalIntegral.integral_add_adjacent_intervals hs hl
  rw [← hadj]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hmono
  have hs10 := weighted_integrable regularOuter10_continuous
  have hs11 := weighted_integrable regularOuter11_continuous
  simp_rw [add_div] at hmono
  rw [intervalIntegral.integral_add hs10 hs11] at hmono
  have hl10 := regularOuter10_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) beta
  have hl11 := regularOuter11_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) beta
  rw [intervalIntegral.integral_add hl10 hl11] at hlarge ⊢
  unfold original10 original11 original
  linarith only [hmono,hlarge]

theorem lowerAmount_le_integral {c : ℝ} (hc0 : 0 ≤ c) :
    lowerAmount c ≤ weightFloor*(∫ x in alpha..beta, lowerProfile c x) := by
  rw [lowerProfile_integral]
  unfold lowerAmount
  apply mul_le_mul_of_nonneg_left _ weightFloor_bounds.1.le
  apply Finset.sum_le_sum
  intro i _
  have hl := FourLogAffine.fixed_log_bounds
  have hp (n : ℕ) := pow_le_pow_left₀ hl.1.le hl.2.1 n
  exact add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hp (i.val+3))
        (lower_coefficients_nonneg hc0 i).1) (by positivity))
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hp (i.val+4))
        (lower_coefficients_nonneg hc0 i).2) (by positivity))

theorem original_pair_lowerAmount {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u) :
    lowerAmount c ≤ original10+original11 := by
  have ha := geometry.2.2.2.1
  have hab := geometry.1.le.trans (geometry.2.1.le.trans geometry.2.2.1.le)
  have hi := intervalIntegral.integral_mono_on hab (lowerProfile_integrable c ha hab)
    ((regularOuter10_continuous.add regularOuter11_continuous).intervalIntegrable
      (μ := volume) alpha beta)
    (fun x hx => lowerProfile_le_outer hc0 hc hx)
  exact (lowerAmount_le_integral hc0).trans
    ((mul_le_mul_of_nonneg_left hi weightFloor_bounds.1.le).trans original_weight_floor)

#check @original_weight_floor
#check @lowerAmount_le_integral
#check @original_pair_lowerAmount
#print axioms original_weight_floor
#print axioms lowerAmount_le_integral
#print axioms original_pair_lowerAmount
end WuSource.SrcFour
