import OriginalBoundaryUpper
open MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
namespace OriginalU8.Weighted
variable {a : ℝ}
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

private theorem weightedUpperIntegrand_majorized (ha : 1/20 ≤ a) {n : ℕ} (hn : 0 < n) (h : ℝ) (x : ℝ × ℝ) :
    upperIntegrand a n h x ≤
      (source a).indicator (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x) x +
        weightedUnitBox.indicator (fun _ => 20000 / (n : ℝ)) x +
        (leftStrip a n).indicator (fun _ => (1500 : ℝ)) x +
        (bottomStrip a n).indicator (fun _ => (1500 : ℝ)) x +
        (obliqueStrip a n h).indicator (fun _ => (1500 : ℝ)) x +
        (fouvryG9WeightedRightStrip n).indicator (fun _ => (1500 : ℝ)) x := by
  have hS := weightedIndicator_nonneg (f := fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x) (fun x hx =>
    mul_nonneg (by norm_num) (fouvryG9WeightedIntegrand_bounds (source_subset_ambient ha hx)).1) x
  have hU := weightedIndicator_nonneg
    (s := weightedUnitBox) (f := fun _ => 20000 / (n : ℝ)) (by intros; positivity) x
  have hL := weightedIndicator_nonneg
    (s := leftStrip a n) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  have hB := weightedIndicator_nonneg
    (s := bottomStrip a n) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  have hO := weightedIndicator_nonneg
    (s := obliqueStrip a n h) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  have hR := weightedIndicator_nonneg
    (s := fouvryG9WeightedRightStrip n) (f := fun _ => (1500 : ℝ)) (by intros; norm_num) x
  by_cases hg : x ∈ region a n h
  · by_cases hs : x ∈ source a
    · have hb := region_subset_ambient hn h hg
      have hu : x ∈ weightedUnitBox :=
        ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
          ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩
      rw [indicator_of_mem hs, indicator_of_mem hu]
      linarith [upperIntegrand_le_integrand_add hn hg]
    · rw [indicator_of_notMem hs]
      have hb := upperIntegrand_le hn hg
      rcases region_excess_subset hn h ⟨hg, hs⟩ with ((hl | hd) | ho) | hr
      · rw [indicator_of_mem hl]
        linarith
      · rw [indicator_of_mem hd]
        linarith
      · rw [indicator_of_mem ho]
        linarith
      · rw [indicator_of_mem hr]
        linarith
  · rw [upperIntegrand_eq_zero hg]
    linarith

theorem integrable_scaledSource (ha : 1/20 ≤ a) :
    Integrable ((source a).indicator
      (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x)) :=
  integrable_indicator_of_integrableOn measurableSet_source
    ((integrableOn_fouvryG9WeightedIntegrand measurableSet_source
      (source_subset_ambient ha)).const_mul _)

/-- Uniform in every positive mesh, with the actual integral as the main term. -/
theorem upperSum_le_low_add_error (ha : 1/20 ≤ a) (hab : a ≤ 1/10) (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 ≤ h) :
    upperSum a n h 0 ≤ (9/5 : ℝ)*low a + 30000*(h+1/(n : ℝ)) := by
  let fSource := (source a).indicator (fun x => (9/5 : ℝ)*fouvryG9WeightedIntegrand x)
  let fUnit := weightedUnitBox.indicator (fun _ => 20000 / (n : ℝ))
  let fLeft := (leftStrip a n).indicator (fun _ => (1500 : ℝ))
  let fBottom := (bottomStrip a n).indicator (fun _ => (1500 : ℝ))
  let fOblique := (obliqueStrip a n h).indicator (fun _ => (1500 : ℝ))
  have hSource : Integrable fSource := integrable_scaledSource ha
  have hUnit : Integrable fUnit := by
    apply integrable_indicator_of_integrableOn (measurableSet_Icc.prod measurableSet_Icc)
    apply integrableOn_const
    · rw [volume_weightedUnitBox]
      norm_num
    · finiteness
  have hLeft : Integrable fLeft := by
    apply integrable_indicator_of_integrableOn (measurableSet_leftStrip n)
    apply integrableOn_const
    · rw [volume_leftStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hBottom : Integrable fBottom := by
    apply integrable_indicator_of_integrableOn (measurableSet_bottomStrip n)
    apply integrableOn_const
    · rw [volume_bottomStrip hab]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hOblique : Integrable fOblique := by
    apply integrable_indicator_of_integrableOn (measurableSet_obliqueStrip n h)
    apply integrableOn_const
    · rw [volume_obliqueStrip n h hh]
      exact ENNReal.ofReal_ne_top
    · finiteness
  let fRight := (fouvryG9WeightedRightStrip n).indicator (fun _ => (1500 : ℝ))
  have hRight : Integrable fRight := by
    apply integrable_indicator_of_integrableOn (measurableSet_fouvryG9WeightedRightStrip n)
    apply integrableOn_const
    · rw [volume_fouvryG9WeightedRightStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hmono : (∫ x, upperIntegrand a n h x) ≤
      ∫ x, (((fSource x + fUnit x) + fLeft x) + fBottom x) + fOblique x + fRight x :=
    integral_mono (integrable_upperIntegrand n hn h)
      (((((hSource.add hUnit).add hLeft).add hBottom).add hOblique).add hRight)
      (weightedUpperIntegrand_majorized ha hn h)
  rw [← upperSum_eq_integral n hn h] at hmono
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
  rw [integral_indicator measurableSet_source,
    integral_const_mul, ← low_eq_setIntegral ha hab,
    integral_indicator_const (20000 / (n : ℝ)) (measurableSet_Icc.prod measurableSet_Icc),
    integral_indicator_const (1500 : ℝ) (measurableSet_leftStrip n),
    integral_indicator_const (1500 : ℝ) (measurableSet_bottomStrip n),
    integral_indicator_const (1500 : ℝ) (measurableSet_obliqueStrip n h),
    integral_indicator_const (1500 : ℝ) (measurableSet_fouvryG9WeightedRightStrip n),
    Measure.real_def, volume_weightedUnitBox,
    Measure.real_def, volume_leftStrip,
    Measure.real_def, volume_bottomStrip hab,
    Measure.real_def, volume_obliqueStrip n h hh,
    Measure.real_def, volume_fouvryG9WeightedRightStrip] at hmono
  simp only [ENNReal.toReal_one, smul_eq_mul] at hmono
  have hAlpha := (goldbachB9AlphaGridStep_pos hn).le
  have hBeta := (goldbachB9BetaGridStep_pos hn).le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (17 / 240 : ℝ) / n),
    ENNReal.toReal_ofReal (mul_nonneg (by linarith : 0 ≤ (1/3 : ℝ)-a)
      (goldbachB9BetaGridStep_pos hn).le),
    ENNReal.toReal_ofReal (mul_nonneg (by linarith : 0 ≤ (1/3 : ℝ)-a)
      (by positivity : 0 ≤ (h+goldbachB9AlphaGridStep n+2*goldbachB9BetaGridStep n)/2))] at hmono
  have herr : 20000 / (n : ℝ) + (17 / 240 : ℝ) / n * 1500 +
      ((1/3-a)*goldbachB9BetaGridStep n)*1500 +
      ((1/3-a)*((h+goldbachB9AlphaGridStep n+2*goldbachB9BetaGridStep n)/2))*1500 +
      (17/240 : ℝ)/n*1500 ≤ 30000*(h+1/(n : ℝ)) := by
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hbn := (goldbachB9BetaGridStep_pos hn).le
    have hm : 0 ≤ (h+goldbachB9AlphaGridStep n+2*goldbachB9BetaGridStep n)/2 := by positivity
    have hB := mul_le_mul_of_nonneg_right (by linarith : 1/3-a ≤ (1 : ℝ)) hbn
    have hO := mul_le_mul_of_nonneg_right (by linarith : 1/3-a ≤ (1 : ℝ)) hm
    have hs : 20000/(n : ℝ)+(17/240 : ℝ)/n*1500+
        goldbachB9BetaGridStep n*1500+
        ((h+goldbachB9AlphaGridStep n+2*goldbachB9BetaGridStep n)/2)*1500+
        (17/240 : ℝ)/n*1500 ≤ 30000*(h+1/(n : ℝ)) := by
      unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
      have hpos := mul_nonneg hh hnr.le
      field_simp
      nlinarith
    linarith
  linarith



/-- The mesh and boundary width are fixed before any prime-size limit. -/
theorem exists_upperSum_le_low_add (ha : 1/20 ≤ a) (hab : a ≤ 1/10)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, 0 < n ∧ ∃ h : ℝ, 0 < h ∧ h ≤ 1/20 ∧
      upperSum a n h 0 ≤ (9/5 : ℝ)*low a + τ := by
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
  have hb := upperSum_le_low_add_error ha hab n hnNat h hh.le
  have he : 30000*(h+1/(n : ℝ)) = 30000*h+30000/(n : ℝ) := by ring
  rw [he] at hb
  linarith


end OriginalU8.Weighted
