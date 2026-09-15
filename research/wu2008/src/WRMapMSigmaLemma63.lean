import WRMapMSigmaWeightedTail

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Interval

def source63RHS (f : ℝ → ℝ) (a b c : ℝ) : ℝ :=
  log ((b - a * b) / (a - a * b)) *
    (∫ t in (1 : ℝ)..3, f t *
      (sigma0 t + (Icc (b * c - 1) 3).indicator (fun _ => (1 : ℝ)) t) / t) +
    ∫ t in (1 : ℝ)..3,
      f t * (Icc (a * c - 1) (b * c - 1)).indicator (fun _ => (1 : ℝ)) t / t *
        log ((1 - a) * (t + 1) / (a * (c - 1 - t)))

theorem sigma_indicator_integral {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {d : ℝ} (hd : d ∈ Icc 1 3) :
    (∫ t in (1 : ℝ)..3,
      f t * (sigma0 t + (Icc d 3).indicator (fun _ => (1 : ℝ)) t) / t) =
      aProfile f + ∫ t in d..3, f t / t := by
  have hi : IntervalIntegrable ((Icc d 3).indicator (fun t => f t / t)) volume 1 3 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (1 : ℝ) ≤ 3)).mp (profile_div_integrable hf)).indicator measurableSet_Icc
  have he (t : ℝ) : f t * (sigma0 t + (Icc d 3).indicator (fun _ => (1 : ℝ)) t) / t =
      f t * sigma0 t / t + (Icc d 3).indicator (fun t => f t / t) t := by
    by_cases ht : t ∈ Icc d 3
    · simp only [indicator_of_mem ht]
      ring
    · simp only [indicator_of_notMem ht]
      ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (sigma_weight_integrable hf) hi,
    indicator_interval_integral hd.1 hd.2 le_rfl]
  rfl

theorem source63RHS_identity {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {a b c : ℝ}
    (hac : 2 ≤ a * c) (habc : a * c ≤ b * c) (hbc : b * c ≤ 4) :
    source63RHS f a b c =
      (aProfile f + ∫ t in (b * c - 1)..3, f t / t) *
        log ((b - a * b) / (a - a * b)) +
      ∫ t in (a * c - 1)..(b * c - 1),
        f t / t * log ((1 - a) * (t + 1) / (a * (c - 1 - t))) := by
  unfold source63RHS
  rw [sigma_indicator_integral hf ⟨by linarith, by linarith⟩]
  have he (t : ℝ) :
      f t * (Icc (a * c - 1) (b * c - 1)).indicator (fun _ => (1 : ℝ)) t / t *
          log ((1 - a) * (t + 1) / (a * (c - 1 - t))) =
        (Icc (a * c - 1) (b * c - 1)).indicator
          (fun t => f t / t * log ((1 - a) * (t + 1) / (a * (c - 1 - t)))) t := by
    by_cases ht : t ∈ Icc (a * c - 1) (b * c - 1)
    · simp only [indicator_of_mem ht, mul_one]
    · simp only [indicator_of_notMem ht, mul_zero, zero_div, zero_mul]
  simp_rw [he]
  rw [indicator_interval_integral (by linarith) (by linarith) (by linarith)]
  ring

private theorem shifted_div_tail (f : ℝ → ℝ) (u : ℝ) :
    (∫ v in u..4, f (v - 1) / (v - 1)) = ∫ t in (u - 1)..3, f t / t := by
  rw [intervalIntegral.integral_comp_sub_right (fun t => f t / t) 1]
  norm_num

theorem gProfile_weighted_formula {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    IntervalIntegrable (fun u => gProfile f u * rationalWeight c u) volume (a * c) (b * c) ∧
    (∫ u in (a * c)..(b * c), gProfile f u * rationalWeight c u) = source63RHS f a b c := by
  have hc : 0 < c := by nlinarith
  have habc : a * c ≤ b * c := mul_le_mul_of_nonneg_right hab.le hc.le
  have hp24 : IntervalIntegrable (fun u => f (u - 1) / (u - 1)) volume 2 4 := by
    convert (profile_div_integrable hf).comp_sub_right 1 using 1 <;> norm_num
  have hp : IntervalIntegrable (fun u => f (u - 1) / (u - 1)) volume (a * c) 4 := by
    apply hp24.mono_set
    rw [uIcc_of_le (habc.trans hbc), uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    exact Icc_subset_Icc hac le_rfl
  have hw := (rationalWeight_continuous (mul_pos ha hc) habc
    (by nlinarith : b * c < c)).intervalIntegrable (μ := volume)
  have hex := weighted_tail_exchange habc hbc hp hw (aProfile f)
  simp_rw [shifted_div_tail] at hex
  change IntervalIntegrable (fun u => gProfile f u * rationalWeight c u)
      volume (a * c) (b * c) ∧ _ at hex
  refine ⟨hex.1, ?_⟩
  simp only [gProfile]
  rw [hex.2, rationalWeight_source_log ha hab hb hc,
    source63RHS_identity hf hac habc hbc]
  congr 1
  have he : (∫ u in (a * c)..(b * c),
      f (u - 1) / (u - 1) * (∫ x in (a * c)..u, rationalWeight c x)) =
      ∫ u in (a * c)..(b * c),
        f (u - 1) / (u - 1) * log ((1 - a) * u / (a * (c - u))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le habc] at hu
    dsimp only
    rw [rationalWeight_partial_log ha hab hb hc hu]
  rw [he]
  have hs := intervalIntegral.integral_comp_add_right
    (a := a * c - 1) (b := b * c - 1)
    (fun u => f (u - 1) / (u - 1) * log ((1 - a) * u / (a * (c - u)))) 1
  simp only [sub_add_cancel, add_sub_cancel_right] at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show c - (t + 1) = c - 1 - t by ring]

theorem lemma63 {δ a b c : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    source63RHS (wuImprovementLimit true δ) a b c ≤
      ∫ t in a..b, wuImprovementLimit false δ (c * t) / (t * (1 - t)) := by
  have hc : 0 < c := by nlinarith
  have habc : a * c ≤ b * c := mul_le_mul_of_nonneg_right hab.le hc.le
  have hf := wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
    (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  have hg := gProfile_weighted_formula hf ha hab hb hac hbc
  have hw := rationalWeight_continuous (mul_pos ha hc) habc (by nlinarith : b * c < c)
  have hhi := (wuImprovementLimit_intervalIntegrable false hd
    (by linarith : δ < 1 / 2) (a := a * c) (b := b * c)
    (by linarith) habc (by linarith)).mul_continuousOn hw
  rw [← hg.2, rationalWeight_rescale ha hab hb hc]
  apply intervalIntegral.integral_mono_on habc hg.1 hhi
  intro u hu
  apply mul_le_mul_of_nonneg_right
  · exact (actual_continuous_extension hd hdhi).2.1 u
      ⟨hac.trans hu.1, hu.2.trans hbc⟩
  · exact div_nonneg hc.le (mul_nonneg (by nlinarith [hu.1]) (by nlinarith [hu.2]))

theorem lemma63_literal {δ a b c : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    log ((b - a * b) / (a - a * b)) *
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t *
        (sigma0 t + (Icc (b * c - 1) 3).indicator (fun _ => (1 : ℝ)) t) / t) +
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t *
        (Icc (a * c - 1) (b * c - 1)).indicator (fun _ => (1 : ℝ)) t / t *
          log ((1 - a) * (t + 1) / (a * (c - 1 - t)))) ≤
      ∫ t in a..b, wuImprovementLimit false δ (c * t) / (t * (1 - t)) :=
  lemma63 hd hdhi ha hab hb hac hbc

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.source63RHS
#check @WuPaper.RMapMSigma.sigma_indicator_integral
#check @WuPaper.RMapMSigma.source63RHS_identity
#check @WuPaper.RMapMSigma.gProfile_weighted_formula
#check @WuPaper.RMapMSigma.lemma63
#check @WuPaper.RMapMSigma.lemma63_literal
#print axioms WuPaper.RMapMSigma.source63RHS
#print axioms WuPaper.RMapMSigma.sigma_indicator_integral
#print axioms WuPaper.RMapMSigma.source63RHS_identity
#print axioms WuPaper.RMapMSigma.gProfile_weighted_formula
#print axioms WuPaper.RMapMSigma.lemma63
#print axioms WuPaper.RMapMSigma.lemma63_literal
