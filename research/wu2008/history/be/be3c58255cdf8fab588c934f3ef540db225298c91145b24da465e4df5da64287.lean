import SrcFourEnclosureTail
import WSrcBuchstabRoot

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFourEnclosure

theorem outer_uniform_upper {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter10 x+regularOuter11 x ≤ (4/7 : ℝ)*outerMass x :=
  (outer_bounds hx (fun y hy z hz t ht =>
    merged_kernel_bounds (fun _ hv => LiLiuPrereqBuchstab.buchstab_nonneg (by linarith only [hv]))
      (fun _ hv => SecondFunctionalFourSevenths.buchstab_le_four_sevenths
        (by linarith only [hv])) hx.1 hy.1 hz.1 hz.2 ht)).2

theorem outer_fine_upper {c x : ℝ}
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : x ∈ Icc alpha SrcFour.outerCut) :
    regularOuter10 x+regularOuter11 x ≤ c*outerMass x := by
  apply (outer_bounds (l := (0 : ℝ)) (u := c)
    ⟨hx.1,hx.2.trans SrcFour.geometry.2.2.1.le⟩ ?_).2
  intro y hy z hz t ht
  have hf : (17/5 : ℝ) ≤ parameter x y z t := by
    by_cases htb : t ≤ beta
    · exact SrcFour.ten_fine ⟨hx.1,hy.1,hz.1,ht.1,htb⟩
    · exact SrcFour.eleven_fine_of_outer
        ⟨hx.1,hy.1,hz.1,hz.2,(lt_of_not_ge htb).le,ht.2⟩ hx.2
  refine ⟨(merged_kernel_bounds
    (l := (0 : ℝ)) (u := (4/7 : ℝ))
    (fun _ hv => LiLiuPrereqBuchstab.buchstab_nonneg (by linarith only [hv]))
    (fun _ hv => SecondFunctionalFourSevenths.buchstab_le_four_sevenths
      (by linarith only [hv])) hx.1 hy.1 hz.1 hz.2 ht).1,?_⟩
  exact SrcFour.fine_kernel hc hx.1 (hx.1.trans hy.1)
    (hx.1.trans (hy.1.trans hz.1)) (hx.1.trans (hy.1.trans (hz.1.trans ht.1))) hf

theorem original_pair_mass_tail {c : ℝ}
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c) :
    original10+original11 ≤ c*mass+((4/7 : ℝ)-c)*tailGeom := by
  have ha : alpha ≤ (1/10 : ℝ) := SrcFour.geometry.1.le
  have hd : (1/10 : ℝ) ≤ SrcFour.outerCut := SrcFour.geometry.2.1.le
  have hb : SrcFour.outerCut ≤ beta := SrcFour.geometry.2.2.1.le
  have ho : Continuous (fun x => regularOuter10 x+regularOuter11 x) :=
    regularOuter10_continuous.add regularOuter11_continuous
  have hs := intervalIntegral.integral_mono_on ha
    (weighted_integrable ho)
    ((weighted_integrable outerMass_continuous).const_mul c) (fun x hx => by
      have h := div_le_div_of_nonneg_right
        (outer_fine_upper hc ⟨hx.1,hx.2.trans hd⟩)
        (show 0 ≤ 1-x by linarith only [hx.2])
      simpa only [mul_div_assoc] using h)
  have hm := intervalIntegral.integral_mono_on hd
    (ho.intervalIntegrable (μ := volume) (1/10 : ℝ) SrcFour.outerCut)
    ((outerMass_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ)
      SrcFour.outerCut).const_mul c)
    (fun x hx => outer_fine_upper hc ⟨ha.trans hx.1,hx.2⟩)
  have ht := intervalIntegral.integral_mono_on hb
    (ho.intervalIntegrable (μ := volume) SrcFour.outerCut beta)
    ((outerMass_continuous.intervalIntegrable (μ := volume)
      SrcFour.outerCut beta).const_mul (4/7 : ℝ))
    (fun x hx => outer_uniform_upper ⟨ha.trans (hd.trans hx.1),hx.2⟩)
  have hoa := intervalIntegral.integral_add_adjacent_intervals
    (ho.intervalIntegrable (μ := volume) (1/10 : ℝ) SrcFour.outerCut)
    (ho.intervalIntegrable (μ := volume) SrcFour.outerCut beta)
  have hma := intervalIntegral.integral_add_adjacent_intervals
    (outerMass_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) SrcFour.outerCut)
    (outerMass_continuous.intervalIntegrable (μ := volume) SrcFour.outerCut beta)
  rw [intervalIntegral.integral_const_mul] at hs hm ht
  rw [← original_pair_add]
  unfold mass original tailGeom
  rw [← hoa,← hma]
  linarith only [hs,hm,ht]

theorem original_pair_upper :
    original10+original11 < (851/1250 : ℝ) := by
  have h := original_pair_mass_tail (fun _ hu => SrcBuchstab.buchstab_le_source_fine hu)
  have hm := mul_lt_mul_of_pos_left mass_rational_enclosure.2
    (by norm_num : (0 : ℝ) < 561522/1000000)
  have ht := mul_lt_mul_of_pos_left tailGeom_upper
    (by norm_num : (0 : ℝ) < 4/7-561522/1000000)
  linarith only [h,hm,ht]

theorem original_pair_nonneg : (0 : ℝ) ≤ original10+original11 := by
  have h := original_pair_lower (l := (0 : ℝ))
    (fun _ hv => LiLiuPrereqBuchstab.buchstab_nonneg (by linarith only [hv]))
  simpa only [zero_mul] using h

#check @original_pair_mass_tail
#check @original_pair_upper
#check @original_pair_nonneg
#print axioms original_pair_mass_tail
#print axioms original_pair_upper
#print axioms original_pair_nonneg
end WuSource.SrcFourEnclosure
