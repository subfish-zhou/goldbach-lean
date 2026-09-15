import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSmallDelta
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthPositiveGain

namespace Wu2008DoubleSieve.TruncatedSixthSmallDeltaGain
open Set Real MeasureTheory
open scoped Classical

/-- The rectangle is fixed before the proof and lies in the original admissible region. -/
theorem rectangle_geometry {δ x y : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) (hx : x ∈ Icc (1/10 : ℝ) (11/100))
    (hy : y ∈ Icc (1/5 : ℝ) (21/100)) :
    truncatedSixthLowerAdmissibleRegion δ x y ∧
      truncatedSixthLowerS δ x y ∈ Icc (2 : ℝ) (1327/500) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor
  · unfold truncatedSixthLowerAdmissibleRegion truncatedSixthLowerRegion
      truncatedSixthLowerAlpha truncatedSixthLowerBeta truncatedSixthLowerSigma
      truncatedSixthLowerC
    norm_num [truncatedSixthLowerAlpha]
    exact ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩,
      by linarith⟩
  · unfold truncatedSixthLowerS truncatedSixthLowerC truncatedSixthLowerAlpha
    constructor <;> norm_num <;> linarith

/-- All denominator factors are positive and bounded by the prescribed rational factors. -/
theorem rectangle_denominator {δ x y : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) (hx : x ∈ Icc (1/10 : ℝ) (11/100))
    (hy : y ∈ Icc (1/5 : ℝ) (21/100)) :
    0 < x * y * (truncatedSixthLowerC δ - x - y) ∧
    x * y * (truncatedSixthLowerC δ - x - y) ≤
      (11/100 : ℝ) * (21/100) * (1/5) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hz0 : 0 < truncatedSixthLowerC δ - x - y := by
    unfold truncatedSixthLowerC
    linarith [hx.2, hy.2]
  have hz1 : truncatedSixthLowerC δ - x - y ≤ (1/5 : ℝ) := by
    unfold truncatedSixthLowerC
    linarith [hx.1, hy.1]
  exact ⟨mul_pos (mul_pos hx0 hy0) hz0,
    mul_le_mul (mul_le_mul hx.2 hy.2 hy0.le (by norm_num)) hz1 hz0.le
      (by norm_num)⟩

/-- The actual lower-improvement seed is consumed pointwise, without continuity. -/
theorem rectangle_kernel_lower {δ x y : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) (hx : x ∈ Icc (1/10 : ℝ) (11/100))
    (hy : y ∈ Icc (1/5 : ℝ) (21/100)) :
    (141/125000 : ℝ) / ((11/100) * (21/100) * (1/5)) ≤
      truncatedSixthMassHKernel δ (x,y) := by
  obtain ⟨ha, hs⟩ := rectangle_geometry hδ hδhi hx hy
  obtain ⟨hd0, hd1⟩ := rectangle_denominator hδ hδhi hx hy
  rw [truncatedSixthMassHKernel, if_pos ha]
  have hsHi : truncatedSixthLowerS δ x y < (7/2 : ℝ) := by linarith [hs.2]
  have hh0 := SecondFunctionalSmallDelta.h_strict hδ hδhi hs.1 hsHi
  have hh : (141/125000 : ℝ) ≤ wuImprovementLimit false δ (truncatedSixthLowerS δ x y) := by
    linarith [hs.2]
  exact div_le_div₀ (by linarith) hh hd0 hd1

/-- Genuine subrectangle integration, followed by comparison with the entire original kernel. -/
theorem rectangle_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    (1/10000 : ℝ) * ((141/125000) / ((11/100) * (21/100) * (1/5))) ≤
      ∫ v : ℝ × ℝ, truncatedSixthMassHKernel δ v := by
  let R : Set (ℝ × ℝ) := Icc (1/10 : ℝ) (11/100) ×ˢ Icc (1/5 : ℝ) (21/100)
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hfin : volume R ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi := (truncatedSixthMass_kernels_integrable
    (δ := δ) hδ (by linarith)).2
  have hc : IntegrableOn (fun _ : ℝ × ℝ =>
      (141/125000 : ℝ) / ((11/100) * (21/100) * (1/5))) R :=
    integrableOn_const hfin
  have hsub := setIntegral_mono_on hc hi.integrableOn hR
    (fun v hv => rectangle_kernel_lower hδ hδhi hv.1 hv.2)
  have hnonneg : ∀ v : ℝ × ℝ, 0 ≤ truncatedSixthMassHKernel δ v :=
    fun v => (truncatedSixthMass_kernels_bounds hδ (by linarith) v).2.1
  have hwhole := setIntegral_le_integral (s := R) hi (Filter.Eventually.of_forall hnonneg)
  rw [setIntegral_const, smul_eq_mul] at hsub
  change volume.real (Icc (1/10 : ℝ) (11/100) ×ˢ Icc (1/5 : ℝ) (21/100)) * _ ≤ _ at hsub
  rw [TruncatedSixthPositiveGain.rectangle_area] at hsub
  exact hsub.trans hwhole

/-- The original admissible gain, retaining the original outer coefficient four. -/
theorem hadmdelta_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    (47/481250 : ℝ) ≤ truncatedSixthLowerHadmdelta δ := by
  rw [(truncatedSixthMass_literal_integrals hδ (by linarith)).2]
  have h := mul_le_mul_of_nonneg_left (rectangle_integral_lower hδ hδhi) (by norm_num : (0 : ℝ) ≤ 4)
  norm_num at h ⊢
  exact h

end Wu2008DoubleSieve.TruncatedSixthSmallDeltaGain
