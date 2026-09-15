import HighIncrementDebit

namespace HighIncrement
open Finset Set Real MeasureTheory Wu2008DoubleSieve MixedSixth MixedPayment
open scoped Classical Topology
noncomputable section

/-- The spare correction factor pays the moving rectangle denominator exactly. -/
theorem kernel_cell_bound {δ : ℝ} (hδ : 0 ≤ δ) {n i : ℕ}
    (hi : i ∈ highCells δ n) (hm : 2*mesh n ≤ truncatedSixthLowerAlpha)
    {v : ℝ × ℝ} (hv : v ∈ truncatedSixthClosureCell n (coarse i)) :
    HighConsumer.highGainKernel v ≤
      (gainWeight δ n i/(truncatedSixthLowerC δ-loX n i-loY n i))*(v.1⁻¹*v.2⁻¹) := by
  have hg := high_geometry hi
  have hb : (loX n i ≤ v.1 ∧ v.1 < hiX n i) ∧ (loY n i ≤ v.2 ∧ v.2 < hiY n i) := hv
  have hx := truncatedSixthLower_parameters.1.trans_le (hg.1.trans hb.1.1)
  have hy : 0 < v.2 := lt_of_lt_of_le (by norm_num) (hg.2.1.trans hb.2.1)
  have hxy := mul_pos hx hy
  have hD : 0 < truncatedSixthLowerC δ-loX n i-loY n i := by
    have ha := truncatedSixthLower_parameters.1
    linarith [hg.2.2.2.2.2.2,(widths n i).1,(widths n i).2,mesh_pos n]
  by_cases hmem : v ∈ Wu08G6High.highDomain
  · rw [HighConsumer.highGainKernel,indicator_of_mem hmem]
    have hu := (Wu08G6High.high_iff v.1 v.2).mp hmem
    have hzlo : 2*truncatedSixthLowerAlpha ≤ (1:ℝ)/2-v.1-v.2 := by
      change 2*QuarterTrim.alpha ≤ _
      linarith [hu.2.2]
    have hz : 0 < (1:ℝ)/2-v.1-v.2 := by linarith [truncatedSixthLower_parameters.1]
    have hsu : source δ n i ≤ QuarterTrim.u v.1 v.2 := by
      unfold source truncatedSixthLowerS QuarterTrim.u
      change (truncatedSixthLowerC δ-hiX n i-hiY n i)/truncatedSixthLowerAlpha ≤
        (1/2-v.1-v.2)/truncatedSixthLowerAlpha
      apply div_le_div_of_nonneg_right _ truncatedSixthLower_parameters.1.le
      unfold truncatedSixthLowerC
      linarith [hb.1.2,hb.2.2]
    have hc := HighConsumer.correction_antitone (by linarith [(source_bounds hδ hi).1]) hsu
    have hc0 := (reserve_pos.trans_le (reserve_le hδ hi)).le
    have hd : truncatedSixthLowerC δ-loX n i-loY n i ≤ (3/2)*((1:ℝ)/2-v.1-v.2) := by
      unfold truncatedSixthLowerC
      linarith [(widths n i).1,(widths n i).2,hb.1.2,hb.2.2]
    have hcd : PositiveH.lowerCorrection (source δ n i)*
        (truncatedSixthLowerC δ-loX n i-loY n i) ≤ gainWeight δ n i*((1:ℝ)/2-v.1-v.2) := by
      have h := mul_le_mul_of_nonneg_left hd hc0
      unfold gainWeight
      nlinarith only [h]
    calc
      PositiveH.lowerCorrection (QuarterTrim.u v.1 v.2)/(v.1*v.2*(1/2-v.1-v.2)) ≤
          PositiveH.lowerCorrection (source δ n i)/(v.1*v.2*(1/2-v.1-v.2)) :=
        div_le_div_of_nonneg_right hc (mul_pos hxy hz).le
      _ ≤ gainWeight δ n i/((truncatedSixthLowerC δ-loX n i-loY n i)*(v.1*v.2)) := by
        apply (div_le_div_iff₀ (mul_pos hxy hz) (mul_pos hD hxy)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hcd hxy.le]
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  · rw [HighConsumer.highGainKernel,indicator_of_notMem hmem]
    exact mul_nonneg (div_nonneg (gainWeight_pos hδ hi).le hD.le) (mul_nonneg (inv_nonneg.mpr hx.le) (inv_nonneg.mpr hy.le))

/-- Exact logarithmic reciprocal mass on the original half-open coarse rectangle. -/
theorem cell_reciprocal_integral {δ : ℝ} {n i : ℕ} (hi : i ∈ highCells δ n) :
    (∫ v in truncatedSixthClosureCell n (coarse i), v.1⁻¹*v.2⁻¹) =
      log (hiX n i/loX n i)*log (hiY n i/loY n i) := by
  have hg := high_geometry hi
  have hx := truncatedSixthLower_parameters.1.trans_le hg.1
  have hy : 0 < loY n i := lt_of_lt_of_le (by norm_num) hg.2.1
  have hxy (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      (∫ x in Ico a b, x⁻¹) = log (b/a) := by
    rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
    apply integral_inv
    rw [uIcc_of_le hab]
    exact fun h => (not_le_of_gt ha) h.1
  change (∫ v in Ico (loX n i) (hiX n i) ×ˢ Ico (loY n i) (hiY n i), v.1⁻¹*v.2⁻¹) = _
  rw [MeasureTheory.Measure.volume_eq_prod, setIntegral_prod_mul]
  exact congrArg₂ (fun x y : ℝ => x*y)
    (hxy (loX n i) (hiX n i) hx (truncatedSixthClosure_lo_lt_hi n (coarse i).1).le)
    (hxy (loY n i) (hiY n i) hy (truncatedSixthClosure_lo_lt_hi n (coarse i).2).le)

theorem cell_reciprocal_integrable {δ : ℝ} {n i : ℕ} (hi : i ∈ highCells δ n) :
    IntegrableOn (fun v : ℝ × ℝ => v.1⁻¹*v.2⁻¹) (truncatedSixthClosureCell n (coarse i)) := by
  have hg := high_geometry hi
  have hx := truncatedSixthLower_parameters.1.trans_le hg.1
  have hy : 0 < loY n i := lt_of_lt_of_le (by norm_num) hg.2.1
  have hc : ContinuousOn (fun v : ℝ × ℝ => v.1⁻¹*v.2⁻¹)
      (Icc (loX n i) (hiX n i) ×ˢ Icc (loY n i) (hiY n i)) := by
    apply ContinuousOn.mul
    · exact continuous_fst.continuousOn.inv₀ (fun v hv => (hx.trans_le hv.1.1).ne')
    · exact continuous_snd.continuousOn.inv₀ (fun v hv => (hy.trans_le hv.2.1).ne')
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (fun _ hv => ⟨⟨hv.1.1,hv.1.2.le⟩,⟨hv.2.1,hv.2.2.le⟩⟩)

/-- No untruncated singular kernel is passed to the domain exhaustion theorem. -/
theorem cell_gain_integral {δ : ℝ} (hδ : 0 ≤ δ) {n i : ℕ}
    (hi : i ∈ highCells δ n) (hm : 2*mesh n ≤ truncatedSixthLowerAlpha) :
    4*(∫ v in truncatedSixthClosureCell n (coarse i), HighConsumer.highGainKernel v) ≤
      gainWeight δ n i*truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
  have h := setIntegral_mono_on HighConsumer.highGain_integrable.integrableOn
    ((cell_reciprocal_integrable hi).const_mul (gainWeight δ n i/(truncatedSixthLowerC δ-loX n i-loY n i)))
    (truncatedSixthClosure_cell_measurable n (coarse i)) (fun _ hv => kernel_cell_bound hδ hi hm hv)
  rw [integral_const_mul,cell_reciprocal_integral hi] at h
  have hh := mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 4 by norm_num)
  calc
    _ ≤ 4*((gainWeight δ n i/(truncatedSixthLowerC δ-loX n i-loY n i))*
        (log (hiX n i/loX n i)*log (hiY n i/loY n i))) := hh
    _ = _ := by unfold truncatedSixthMassRectangleCoefficient; ring

/-- Actual high-cell union, including every original selected cell, normalized to gainScalar. -/
theorem cover_gain_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (hm : 2*mesh n ≤ truncatedSixthLowerAlpha) :
    4*(∫ v, (highCover δ n).indicator HighConsumer.highGainKernel v) ≤ gainScalar δ n := by
  rw [integral_indicator (highCover_measurable δ n)]
  have hd : (highCells δ n : Set ℕ).PairwiseDisjoint
      (fun i => truncatedSixthClosureCell n (coarse i)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    exact hij (Nat.pairEquiv.symm.injective (truncatedSixthClosure_cell_unique hvi hvj))
  rw [highCover,integral_biUnion_finset _
    (fun i _ => truncatedSixthClosure_cell_measurable n (coarse i)) hd
    (fun _ _ => HighConsumer.highGain_integrable.integrableOn),mul_sum]
  exact sum_le_sum (fun i hi => cell_gain_integral hδ hi hm)

end
end HighIncrement
