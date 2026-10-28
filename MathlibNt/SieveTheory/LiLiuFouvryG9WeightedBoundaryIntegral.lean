import MathlibNt.Analysis.IntegralExcessCover
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryKernel
open MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight PrimeReciprocalLogRectangle
set_option maxHeartbeats 800000

private def weightedUnitBox : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

private theorem volume_weightedUnitBox :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  norm_num [Real.volume_Icc]

theorem integrable_fouvryG9WeightedScaledSource :
    Integrable (fouvryG9WeightedSource.indicator
      (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x)) :=
  integrable_indicator_of_integrableOn measurableSet_fouvryG9WeightedSource
    ((integrableOn_fouvryG9WeightedIntegrand measurableSet_fouvryG9WeightedSource
      fouvryG9WeightedSource_subset_ambient).const_mul _)

/-- Uniform in every positive mesh, with the actual integral as the main term. -/
theorem fouvryG9RelaxedIntegralUpperSum_le_low_add_error (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 ≤ h) :
    fouvryG9RelaxedIntegralUpperSum n h 0 ≤ (9/5 : ℝ)*fouvryG9RelaxedIntegralLow + 30000*(h+1/(n : ℝ)) := by
  let E : Fin 4 → Set (ℝ × ℝ) := ![goldbachB9LeftStrip n, goldbachB9BottomStrip n,
    fouvryG9WeightedObliqueStrip n h, fouvryG9WeightedRightStrip n]
  have hbound := MathlibNt.Analysis.IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover
    volume (fouvryG9WeightedRegion n h) fouvryG9WeightedSource weightedUnitBox E
    (fouvryG9WeightedUpperIntegrand n h) (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x)
    (20000 / (n : ℝ)) 1500 (integrable_fouvryG9WeightedUpperIntegrand n hn h)
    ((integrable_indicator_iff measurableSet_fouvryG9WeightedSource).mp
      integrable_fouvryG9WeightedScaledSource)
    measurableSet_fouvryG9WeightedSource (measurableSet_Icc.prod measurableSet_Icc)
    (by dsimp [weightedUnitBox]; rw [volume_weightedUnitBox]; norm_num)
    (by intro i; fin_cases i <;> simp [E, measurableSet_goldbachB9LeftStrip,
      measurableSet_goldbachB9BottomStrip, measurableSet_fouvryG9WeightedObliqueStrip,
      measurableSet_fouvryG9WeightedRightStrip])
    (by
      intro i
      fin_cases i <;> dsimp [E]
      · rw [volume_goldbachB9LeftStrip]; exact ENNReal.ofReal_ne_top
      · rw [volume_goldbachB9BottomStrip]; exact ENNReal.ofReal_ne_top
      · rw [volume_fouvryG9WeightedObliqueStrip n h hh]; exact ENNReal.ofReal_ne_top
      · rw [volume_fouvryG9WeightedRightStrip]; exact ENNReal.ofReal_ne_top)
    (by positivity) (by norm_num)
    (fun _ hx => mul_nonneg (by norm_num)
      (fouvryG9WeightedIntegrand_bounds (fouvryG9WeightedSource_subset_ambient hx)).1)
    (fun _ hx => fouvryG9WeightedUpperIntegrand_eq_zero hx)
    (by
      intro x hx
      have hb := fouvryG9WeightedSource_subset_ambient hx.2
      exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩)
    (fun _ hx => fouvryG9WeightedUpperIntegrand_le_integrand_add hn hx.1)
    (by
      intro x hx
      rcases fouvryG9WeightedRegion_excess_subset hn h hx with ((hl | hd) | ho) | hr
      · exact ⟨0, hl⟩
      · exact ⟨1, hd⟩
      · exact ⟨2, ho⟩
      · exact ⟨3, hr⟩)
    (fun _ hx => fouvryG9WeightedUpperIntegrand_le hn hx.1)
  rw [← fouvryG9RelaxedIntegralUpperSum_eq_integral n hn h,
    integral_const_mul, ← fouvryG9RelaxedIntegralLow_eq_setIntegral] at hbound
  simp only [E, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons,
    Measure.real_def, weightedUnitBox, volume_weightedUnitBox, ENNReal.toReal_one, one_mul,
    volume_goldbachB9LeftStrip, volume_goldbachB9BottomStrip,
    volume_fouvryG9WeightedObliqueStrip n h hh, volume_fouvryG9WeightedRightStrip] at hbound
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (17 / 240 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (41 / 636 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (41/318 : ℝ)*h + (1927 / 19080 : ℝ) / n)] at hbound
  have herr : 20000 / (n : ℝ) + (17 / 240 : ℝ) / n * 1500 +
      (41 / 636 : ℝ) / n * 1500 + ((41/318 : ℝ)*h + (1927 / 19080 : ℝ) / n) * 1500 +
      (17/240 : ℝ)/n*1500 ≤ 30000*(h+1/(n : ℝ)) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 ≤ h*(n : ℝ) := mul_nonneg hh hnreal.le
    field_simp
    nlinarith
  linarith


/-- The mesh and boundary width are fixed before any prime-size limit. -/
theorem exists_fouvryG9RelaxedIntegralUpperSum_le_low_add
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, 0 < n ∧ ∃ h : ℝ, 0 < h ∧ h ≤ 1/20 ∧
      fouvryG9RelaxedIntegralUpperSum n h 0 ≤ (9/5 : ℝ)*fouvryG9RelaxedIntegralLow + τ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((60000 : ℝ)/τ)
  have hnr : (0 : ℝ) < n := (div_pos (by norm_num) hτ).trans hn
  have hnNat : 0 < n := by exact_mod_cast hnr
  let h : ℝ := min (1/20) (τ/60000)
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hhsmall : h ≤ 1/20 := min_le_left _ _
  have hherr : 30000*h ≤ τ/2 := by
    have ht : h ≤ τ/60000 := min_le_right _ _
    linarith
  have hnerr : 30000/(n : ℝ) ≤ τ/2 := by
    apply (div_le_iff₀ hnr).mpr
    have ht := (div_lt_iff₀ hτ).mp hn
    nlinarith
  refine ⟨n, hnNat, h, hh, hhsmall, ?_⟩
  have hb := fouvryG9RelaxedIntegralUpperSum_le_low_add_error n hnNat h hh.le
  have he : 30000*(h+1/(n : ℝ)) = 30000*h+30000/(n : ℝ) := by ring
  rw [he] at hb
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

