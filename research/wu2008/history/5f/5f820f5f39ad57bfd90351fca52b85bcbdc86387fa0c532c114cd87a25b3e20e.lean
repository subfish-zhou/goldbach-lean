import E07FifthSourceTransport

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

def sumShear : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun v := (v.2, v.1-v.2)
  invFun v := (v.1+v.2, v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

def sumKernel (v : ℝ × ℝ) : ℝ := fifthPairKernel 0 (sumShear v)
def sliceLower (z : ℝ) : ℝ := max a (z-b)
def reducedKernel (z : ℝ) : ℝ :=
  wuLowerCoefficient ((1/2-z)/a)/(z*(1/2-z)) *
    log ((z-sliceLower z)/sliceLower z)

theorem sum_shear_preserving :
    MeasurePreserving sumShear (volume : Measure (ℝ × ℝ)) volume := by
  have h := measurePreserving_prod_neg_add_swap (volume : Measure ℝ) (volume : Measure ℝ)
  convert h using 1
  funext v
  dsimp only [sumShear, MeasurableEquiv.coe_mk]
  congr 1
  ring

theorem sum_kernel_integrable : Integrable sumKernel :=
  sum_shear_preserving.integrable_comp_of_integrable
    (fifthPair_kernel_integrable (by norm_num) (by norm_num))

theorem sum_kernel_integral :
    Wu08TerminalAlignment.fifthMain = 4*∫ v : ℝ × ℝ, sumKernel v := by
  have h := sum_shear_preserving.integral_comp sumShear.measurableEmbedding (fifthPairKernel 0)
  change (∫ v : ℝ × ℝ, sumKernel v) = ∫ v : ℝ × ℝ, fifthPairKernel 0 v at h
  rw [h]
  exact fifthPair_literal_integral (by norm_num) (by norm_num)

theorem slice_geometry {z : ℝ} (hz : z ∈ Icc (2*a) (2*b)) :
    0 < sliceLower z ∧ sliceLower z ≤ z/2 ∧ 0 < z ∧ 0 < 1/2-z := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hb : b < 1/4 := by norm_num [b, truncatedSixthLowerBeta]
  refine ⟨ha.trans_le (le_max_left _ _), max_le (by linarith [hz.1])
    (by linarith [hz.2]), by linarith [hz.1], by linarith [hz.2]⟩

theorem sum_region_iff (z x : ℝ) :
    (x,z-x) ∈ fifthPairRegion ↔
      z ∈ Icc (2*a) (2*b) ∧ x ∈ Icc (sliceLower z) (z/2) := by
  change (a ≤ x ∧ x ≤ z-x ∧ z-x ≤ b) ↔ _
  simp only [mem_Icc, sliceLower, max_le_iff]
  constructor
  · rintro ⟨hx, hxy, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨⟨hx, by linarith⟩, by linarith⟩⟩
  · rintro ⟨_, ⟨⟨hx, hz⟩, hxy⟩⟩
    exact ⟨hx, by linarith, by linarith⟩

theorem pair_reciprocal_ftc {z l : ℝ} (hl : 0 < l) (hlz : l ≤ z/2) :
    (∫ x in l..(z/2), 1/(x*(z-x))) = log ((z-l)/l)/z := by
  have hz : 0 < z := by linarith
  have hn (x : ℝ) (hx : x ∈ uIcc l (z/2)) : 0 < x ∧ 0 < z-x := by
    rw [uIcc_of_le hlz] at hx
    exact ⟨hl.trans_le hx.1, by linarith [hx.2]⟩
  have hi : IntervalIntegrable (fun x => 1/(x*(z-x))) volume l (z/2) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun x hx => mul_ne_zero (hn x hx).1.ne' (hn x hx).2.ne')
  have hd (x : ℝ) (hx : x ∈ uIcc l (z/2)) :
      HasDerivAt (fun x => (log x-log (z-x))/z) (1/(x*(z-x))) x := by
    have hh := ((hasDerivAt_log (hn x hx).1.ne').sub
      (((hasDerivAt_const x z).sub (hasDerivAt_id x)).log
        (by simpa only [id_eq] using (hn x hx).2.ne'))).div_const z
    convert hh using 1 <;> first | rfl |
      (simp only [id_eq]; field_simp [hz.ne', (hn x hx).1.ne', (hn x hx).2.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    show z-z/2=z/2 by ring, sub_self, zero_div, zero_sub]
  rw [log_div (by linarith : z-l ≠ 0) hl.ne']
  ring

theorem sum_inner_integral {z : ℝ} (hz : z ∈ Icc (2*a) (2*b)) :
    (∫ x, sumKernel (z,x)) = reducedKernel z := by
  have hg := slice_geometry hz
  have hs : Function.support (fun x => sumKernel (z,x)) ⊆ Icc (sliceLower z) (z/2) := by
    intro x hx
    by_contra hn
    have hv : (x,z-x) ∉ fifthPairRegion := fun hv => hn ((sum_region_iff z x).mp hv).2
    exact hx (by simp [sumKernel, sumShear, fifthPairKernel, hv])
  rw [truncatedSixthMass_integral_eq_interval hg.2.1 hs]
  have he : (∫ x in sliceLower z..(z/2), sumKernel (z,x)) =
      ∫ x in sliceLower z..(z/2),
        (wuLowerCoefficient ((1/2-z)/a)/(1/2-z))*(1/(x*(z-x))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hg.2.1] at hx
    have hv := (sum_region_iff z x).mpr ⟨hz, hx⟩
    have ho := fifthPair_kernel_original (δ := 0) (by norm_num) (by norm_num) hv
    change fifthPairKernel 0 (x,z-x) = _
    rw [ho]
    simp only [truncatedSixthLowerS, truncatedSixthLowerC, sub_zero,
      show (1/2 : ℝ)-x-(z-x)=1/2-z by ring, a]
    ring
  rw [he, intervalIntegral.integral_const_mul, pair_reciprocal_ftc hg.1 hg.2.1]
  unfold reducedKernel
  ring

theorem fifth_main_one_dimensional :
    Wu08TerminalAlignment.fifthMain = 4*∫ z in (2*a)..(2*b), reducedKernel z := by
  rw [sum_kernel_integral]
  rw [show (∫ v : ℝ × ℝ, sumKernel v) = ∫ z, ∫ x, sumKernel (z,x) from
    integral_prod _ sum_kernel_integrable]
  have hs : Function.support (fun z => ∫ x, sumKernel (z,x)) ⊆ Icc (2*a) (2*b) := by
    intro z hz
    by_contra hn
    apply hz
    change (∫ x, sumKernel (z,x)) = 0
    have he : (fun x => sumKernel (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ fifthPairRegion := fun hv => hn ((sum_region_iff z x).mp hv).1
      simp [sumKernel, sumShear, fifthPairKernel, hv]
    rw [he]
    simp
  have hab : 2*a ≤ 2*b := by linarith [truncatedSixthLower_parameters.2.1]
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hab] at hz
  exact sum_inner_integral hz

end
end WuTarget.Wu08FifthSource
