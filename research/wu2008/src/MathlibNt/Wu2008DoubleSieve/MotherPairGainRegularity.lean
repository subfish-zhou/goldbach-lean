import MathlibNt.Wu2008DoubleSieve.MotherPairGainSmooth
import MathlibNt.Wu2008DoubleSieve.Gamma78GainIntegral

namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology

theorem gain_ratio_continuousAt (p : SecondFunctionalParameters) (j : Term)
    {v : ℝ × ℝ} (hv : v.1 ≠ 0) :
    ContinuousAt (fun v : ℝ × ℝ => Hratio p j v.1 v.2) v := by
  cases j <;> unfold Hratio <;> fun_prop

theorem gain_ratio_ne_ae {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (c : ℝ) : ∀ᵐ v : ℝ × ℝ, Hratio p j v.1 v.2 ≠ c := by
  have hS : p.S ≠ 0 := ne_of_gt (by linarith [h.three_le_S])
  have hf : ∀ᵐ v : ℝ × ℝ, p.S*(1-v.1-v.2) ≠ c := by
    filter_upwards [gamma5Gain_affine_ne_ae (-p.S) (-p.S) (c-p.S) (neg_ne_zero.mpr hS)]
      with v hv
    intro he
    apply hv
    linarith
  cases j with
  | gammaFive => exact hf
  | gammaSix => exact hf
  | gammaSeven => exact gamma78Gain_ratio_ne_ae c
  | gammaEight => exact gamma78Gain_ratio_ne_ae c

theorem gain_H_pullback_ae {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∀ᵐ v : ℝ × ℝ, ContinuousAt (gamma5GainH δ) (Hratio p j v.1 v.2) := by
  have hf : ∀ᵐ v : ℝ × ℝ, ContinuousAt (gamma5GainH δ) (p.S*(1-v.1-v.2)) := by
    have hm : Monotone (fun s => -gamma5GainH δ s) := (gamma5Gain_H_antitone hδ hδhi).neg
    have hh := truncatedSixthMass_monotone_affine_ae hm 1 (1/p.S)
      (one_div_ne_zero (ne_of_gt (by linarith [h.three_le_S])))
    filter_upwards [hh] with v hv
    have he : (1-v.1-v.2)/(1/p.S) = p.S*(1-v.1-v.2) := by
      simp only [div_eq_mul_inv,one_mul,inv_inv]
      ring
    rw [he] at hv
    have hn := hv.neg
    have heq : (-(fun s => -gamma5GainH δ s)) = gamma5GainH δ := by
      funext s
      exact neg_neg _
    rwa [heq] at hn
  cases j with
  | gammaFive => exact hf
  | gammaSix => exact hf
  | gammaSeven => exact gamma78Gain_H_pullback_ae hδ hδhi
  | gammaEight => exact gamma78Gain_H_pullback_ae hδ hδhi

/-- All excluded boundaries are null affine or selected-ratio level sets. -/
theorem gain_strict_ae {p : SecondFunctionalParameters} (h : AnalyticParameters p) (j : Term) :
    ∀ᵐ v : ℝ × ℝ, v ∈ gainRegion p j →
      1/p.S < v.1 ∧ v.1 < upperP p j ∧ lowerQ p j < v.2 ∧ v.2 < upperQ p j ∧
      v.1 < v.2 ∧ 2*v.2 < 1 ∧ v.2+2*v.1 < 1 ∧
      1 < Hratio p j v.1 v.2 ∧ Hratio p j v.1 v.2 < 3 := by
  filter_upwards [gamma5Gain_vertical_ne_ae (1/p.S),
    gamma5Gain_vertical_ne_ae (upperP p j),
    gamma5Gain_affine_ne_ae 0 1 (lowerQ p j) (by norm_num),
    gamma5Gain_affine_ne_ae 0 1 (upperQ p j) (by norm_num),
    gamma5Gain_affine_ne_ae 1 (-1) 0 (by norm_num),
    gamma5Gain_affine_ne_ae 0 2 1 (by norm_num),
    gamma5Gain_affine_ne_ae 2 1 1 (by norm_num),
    gain_ratio_ne_ae h j 1, gain_ratio_ne_ae h j 3] with v ha hb hc hd he hf hg hi hk
  intro hv
  have hr := (pairRegion_iff h j v.1 v.2).mp hv.1
  have hratio := gain_ratio_mem h j hv
  simp only [zero_mul,one_mul,zero_add] at hc hd hf hg
  refine ⟨lt_of_le_of_ne hr.1.1 ha.symm,lt_of_le_of_ne hr.1.2 hb,
    lt_of_le_of_ne ((le_max_left _ _).trans hr.2.1) hc.symm,
    lt_of_le_of_ne hr.2.2 hd, ?_,lt_of_le_of_ne hv.2.1 hf, ?_,
    lt_of_le_of_ne hratio.1 hi.symm,lt_of_le_of_ne hratio.2 hk⟩
  · have hle := (le_max_right _ _).trans hr.2.1
    apply lt_of_le_of_ne hle
    intro heq
    apply he
    rw [heq]
    ring
  · apply lt_of_le_of_ne hv.2.2
    intro heq
    exact hg (by linarith)

end Wu2008DoubleSieve.MotherPair
