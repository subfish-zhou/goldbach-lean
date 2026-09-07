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

private theorem weightedIndicator_nonneg {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) (x : ℝ × ℝ) : 0 ≤ s.indicator f x := by
  classical
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx]
    exact h x hx
  · rw [indicator_of_notMem hx]

private theorem weightedUpperIntegrand_majorized {n : ℕ} (hn : 0 < n) (h : ℝ) (x : ℝ × ℝ) :
    fouvryG9WeightedUpperIntegrand n h x ≤
      fouvryG9WeightedSource.indicator (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x) x +
        weightedUnitBox.indicator (fun _ => 20000 / (n : ℝ)) x +
        (goldbachB9LeftStrip n).indicator (fun _ => (1500 : ℝ)) x +
        (goldbachB9BottomStrip n).indicator (fun _ => (1500 : ℝ)) x +
        (fouvryG9WeightedObliqueStrip n h).indicator (fun _ => (1500 : ℝ)) x +
        (fouvryG9WeightedRightStrip n).indicator (fun _ => (1500 : ℝ)) x := by
  have hS := weightedIndicator_nonneg (f := fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x) (fun x hx =>
    mul_nonneg (by norm_num) (fouvryG9WeightedIntegrand_bounds (fouvryG9WeightedSource_subset_ambient hx)).1) x
  have hU := weightedIndicator_nonneg
    (s := weightedUnitBox) (f := fun _ => 20000 / (n : ℝ)) (by intros; positivity) x
  have hL := weightedIndicator_nonneg
    (s := goldbachB9LeftStrip n) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  have hB := weightedIndicator_nonneg
    (s := goldbachB9BottomStrip n) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  have hO := weightedIndicator_nonneg
    (s := fouvryG9WeightedObliqueStrip n h) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  have hR := weightedIndicator_nonneg
    (s := fouvryG9WeightedRightStrip n) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  by_cases hg : x ∈ fouvryG9WeightedRegion n h
  · by_cases hs : x ∈ fouvryG9WeightedSource
    · have hb := fouvryG9WeightedRegion_subset_ambient hn h hg
      have hu : x ∈ weightedUnitBox :=
        ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
          ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩
      rw [indicator_of_mem hs, indicator_of_mem hu]
      linarith [fouvryG9WeightedUpperIntegrand_le_integrand_add hn hg]
    · rw [indicator_of_notMem hs]
      have hb := fouvryG9WeightedUpperIntegrand_le hn hg
      rcases fouvryG9WeightedRegion_excess_subset hn h ⟨hg, hs⟩ with ((hl | hd) | ho) | hr
      · rw [indicator_of_mem hl]
        linarith
      · rw [indicator_of_mem hd]
        linarith
      · rw [indicator_of_mem ho]
        linarith
      · rw [indicator_of_mem hr]
        linarith
  · rw [fouvryG9WeightedUpperIntegrand_eq_zero hg]
    linarith

theorem integrable_fouvryG9WeightedScaledSource :
    Integrable (fouvryG9WeightedSource.indicator
      (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x)) :=
  integrable_indicator_of_integrableOn measurableSet_fouvryG9WeightedSource
    ((integrableOn_fouvryG9WeightedIntegrand measurableSet_fouvryG9WeightedSource
      fouvryG9WeightedSource_subset_ambient).const_mul _)

/-- Uniform in every positive mesh, with the actual integral as the main term. -/
theorem fouvryG9RelaxedIntegralUpperSum_le_low_add_error (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 ≤ h) :
    fouvryG9RelaxedIntegralUpperSum n h 0 ≤ (9/5 : ℝ)*fouvryG9RelaxedIntegralLow + 30000*(h+1/(n : ℝ)) := by
  let fSource := fouvryG9WeightedSource.indicator (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x)
  let fUnit := weightedUnitBox.indicator (fun _ => 20000 / (n : ℝ))
  let fLeft := (goldbachB9LeftStrip n).indicator (fun _ => (1500 : ℝ))
  let fBottom := (goldbachB9BottomStrip n).indicator (fun _ => (1500 : ℝ))
  let fOblique := (fouvryG9WeightedObliqueStrip n h).indicator (fun _ => (1500 : ℝ))
  have hSource : Integrable fSource := integrable_fouvryG9WeightedScaledSource
  have hUnit : Integrable fUnit := by
    apply integrable_indicator_of_integrableOn (measurableSet_Icc.prod measurableSet_Icc)
    apply integrableOn_const
    · rw [volume_weightedUnitBox]
      norm_num
    · finiteness
  have hLeft : Integrable fLeft := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB9LeftStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB9LeftStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hBottom : Integrable fBottom := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB9BottomStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB9BottomStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hOblique : Integrable fOblique := by
    apply integrable_indicator_of_integrableOn (measurableSet_fouvryG9WeightedObliqueStrip n h)
    apply integrableOn_const
    · rw [volume_fouvryG9WeightedObliqueStrip n h hh]
      exact ENNReal.ofReal_ne_top
    · finiteness
  let fRight := (fouvryG9WeightedRightStrip n).indicator (fun _ => (1500 : ℝ))
  have hRight : Integrable fRight := by
    apply integrable_indicator_of_integrableOn (measurableSet_fouvryG9WeightedRightStrip n)
    apply integrableOn_const
    · rw [volume_fouvryG9WeightedRightStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hmono : (∫ x, fouvryG9WeightedUpperIntegrand n h x) ≤
      ∫ x, (((fSource x + fUnit x) + fLeft x) + fBottom x) + fOblique x + fRight x :=
    integral_mono (integrable_fouvryG9WeightedUpperIntegrand n hn h)
      (((((hSource.add hUnit).add hLeft).add hBottom).add hOblique).add hRight)
      (weightedUpperIntegrand_majorized hn h)
  rw [← fouvryG9RelaxedIntegralUpperSum_eq_integral n hn h] at hmono
  have hLast := integral_add ((((hSource.add hUnit).add hLeft).add hBottom).add hOblique) hRight
  simp only [Pi.add_apply] at hLast
  rw [hLast] at hmono
  have hOuter := integral_add (((hSource.add hUnit).add hLeft).add hBottom) hOblique
  have hMid := integral_add ((hSource.add hUnit).add hLeft) hBottom
  have hInner := integral_add (hSource.add hUnit) hLeft
  have hFirst := integral_add hSource hUnit
  simp only [Pi.add_apply] at hOuter hMid hInner hFirst
  rw [hOuter, hMid, hInner, hFirst] at hmono
  dsimp [fSource, fUnit, fLeft, fBottom, fOblique, fRight, weightedUnitBox] at hmono
  rw [integral_indicator measurableSet_fouvryG9WeightedSource,
    integral_const_mul, ← fouvryG9RelaxedIntegralLow_eq_setIntegral,
    integral_indicator_const (20000 / (n : ℝ)) (measurableSet_Icc.prod measurableSet_Icc),
    integral_indicator_const (1500 : ℝ) (measurableSet_goldbachB9LeftStrip n),
    integral_indicator_const (1500 : ℝ) (measurableSet_goldbachB9BottomStrip n),
    integral_indicator_const (1500 : ℝ) (measurableSet_fouvryG9WeightedObliqueStrip n h),
    integral_indicator_const (1500 : ℝ) (measurableSet_fouvryG9WeightedRightStrip n),
    Measure.real_def, volume_weightedUnitBox,
    Measure.real_def, volume_goldbachB9LeftStrip,
    Measure.real_def, volume_goldbachB9BottomStrip,
    Measure.real_def, volume_fouvryG9WeightedObliqueStrip n h hh,
    Measure.real_def, volume_fouvryG9WeightedRightStrip] at hmono
  simp only [ENNReal.toReal_one, smul_eq_mul] at hmono
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (17 / 240 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (41 / 636 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (41/318 : ℝ)*h + (1927 / 19080 : ℝ) / n)] at hmono
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

