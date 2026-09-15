import LowComplementGeometry

namespace LowComplement
open Finset Real Wu2008DoubleSieve MixedSixth Filter
open scoped Classical Topology
noncomputable section

def lowCoefficient (δ : ℝ) (n i : ℕ) : ℝ :=
  wuLowerCoefficient (truncatedSixthLowerS δ (hiX n i) (hiY n i)) +
    wuImprovementLimit false δ (truncatedSixthLowerS δ (hiX n i) (hiY n i))

theorem lowMain_eq (N n : ℕ) (δ : ℝ) :
    lowMain N n δ = ∑ i ∈ lowCells δ n, lowCoefficient δ n i *
      truncatedSixthMassPackingTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
  unfold lowMain
  rw [sum_packing]
  apply sum_congr rfl
  intro i _
  simp only [sourceS,outer,MixedSixth.inner,x,y,Nat.unpair_pair,MixedEta.theta,
    lowCoefficient,truncatedSixthMassPackingTheta,mul_sum]
  simp_rw [MixedEta.theta_swap]

theorem lowCoefficient_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    {n i : ℕ} (hi : i ∈ lowCells δ n) : 0 ≤ lowCoefficient δ n i := by
  exact (truncatedSixthLower_effective_bounds hδ hδhi
    (truncatedSixthLower_region_bounds hδ.le (low_geometry hi).2.2.1).2.2.2).1

theorem weight_le_lowCoefficient {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    {n : ℕ} {j : ℕ × ℕ} (hj : j ∈ truncatedSixthClosureInner true δ n) :
    truncatedSixthClosureWeight true δ n j ≤ lowCoefficient δ n (Nat.pair j.1 j.2) := by
  have hg := truncatedSixthClosure_inner_geometry hj
  have hs := (truncatedSixthLower_region_bounds hδ.le hg.2.2).2.2.2
  have h := truncatedSixthClosure_inf_le
    (fun t => (truncatedSixthClosure_coefficient_bounds hδ hδhi true t).1)
    ⟨le_rfl,truncatedSixthClosure_s_order (δ := δ) (truncatedSixthClosure_corners_order n j)⟩
  change truncatedSixthClosureWeight true δ n j ≤ truncatedSixthClosureCoefficient true δ
    (truncatedSixthLowerS δ (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2)) at h
  simpa only [lowCoefficient,hiX,hiY,coarse,Nat.unpair_pair,truncatedSixthClosureCoefficient,
    if_true,truncatedSixthMassEffective,truncatedSixthMass_clip_eq hs] using h

theorem low_sum_dominates {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100) (n : ℕ) :
    truncatedSixthClosureSum true δ n ≤
      ∑ i ∈ lowCells δ n, lowCoefficient δ n i *
        truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
  unfold lowCells
  rw [sum_image]
  · apply sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_right (weight_le_lowCoefficient hδ hδhi hj)
      (truncatedSixthClosure_rcoef_nonneg hj)
    simpa only [loX,hiX,loY,hiY,coarse,Nat.unpair_pair,truncatedSixthClosureRcoef] using h
  · intro a _ b _ h
    exact Nat.pairEquiv.injective h

theorem low_weighted_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    (hε : 0 < ε) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthClosureSum true δ n-ε)*truncatedSixthMassScale N ≤ lowMain N n δ := by
  have hg (i : ℕ) (hi : i ∈ lowCells δ n) :
      loX n i ≤ hiX n i ∧ loY n i ≤ hiY n i ∧
      truncatedSixthLowerAlpha ≤ loX n i ∧ truncatedSixthLowerBeta ≤ loY n i ∧
      truncatedSixthLowerAdmissibleRegion δ (hiX n i) (hiY n i) :=
    ⟨(truncatedSixthClosure_lo_lt_hi n (coarse i).1).le,
      (truncatedSixthClosure_lo_lt_hi n (coarse i).2).le,low_geometry hi⟩
  have ha := truncatedSixthMass_family_theta_sharp hε (lowCells δ n)
    (loX n) (hiX n) (loY n) (hiY n) (lowCoefficient δ n) hg
    (fun _ hi => lowCoefficient_nonneg hδ hδhi hi)
  filter_upwards [ha,eventually_ge_atTop (4:ℕ)] with N hN hN4
  rw [lowMain_eq]
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right (low_sum_dominates hδ hδhi n) ε)
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

end
end LowComplement
