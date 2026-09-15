import RMapMSigmaLemma63

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Interval

theorem source63_geometry {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    0 < c ∧ a * c < b * c ∧ b * c < c ∧
      a * c - 1 ∈ Icc 1 3 ∧ b * c - 1 ∈ Icc 1 3 := by
  have hc : 0 < c := by nlinarith
  have hm := mul_lt_mul_of_pos_right hab hc
  exact ⟨hc, hm, by nlinarith, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩

theorem source63_log_nonneg {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    0 ≤ log ((b - a * b) / (a - a * b)) := by
  have hg := source63_geometry ha hab hb hac hbc
  rw [← rationalWeight_source_log ha hab hb hg.1]
  apply intervalIntegral.integral_nonneg hg.2.1.le
  intro u hu
  exact div_nonneg hg.1.le (mul_nonneg (by linarith [hu.1]) (by linarith [hu.2, hg.2.2.1]))

theorem source63_partial_log_nonneg {a b c t : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4)
    (ht : t ∈ Icc (a * c - 1) (b * c - 1)) :
    0 ≤ log ((1 - a) * (t + 1) / (a * (c - 1 - t))) := by
  have hg := source63_geometry ha hab hb hac hbc
  have hu : t + 1 ∈ Icc (a * c) (b * c) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [show c - 1 - t = c - (t + 1) by ring,
    ← rationalWeight_partial_log ha hab hb hg.1 hu]
  apply intervalIntegral.integral_nonneg hu.1
  intro u hx
  exact div_nonneg hg.1.le
    (mul_nonneg (by linarith [hx.1]) (by linarith [hx.2, hu.2, hg.2.2.1]))

theorem lemma63_lhs_integrable {δ a b c : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    IntervalIntegrable (fun t => wuImprovementLimit false δ (c * t) / (t * (1 - t)))
      volume a b := by
  have hg := source63_geometry ha hab hb hac hbc
  have hi := wuImprovementLimit_intervalIntegrable false hd (by linarith : δ < 1 / 2)
    (a := a * c) (b := b * c) (by linarith) hg.2.1.le (by linarith)
  have hcomp : IntervalIntegrable (fun t => wuImprovementLimit false δ (c * t)) volume a b := by
    convert hi.comp_mul_left (c := c) using 1 <;> field_simp
  have hw : ContinuousOn (fun t : ℝ => 1 / (t * (1 - t))) (uIcc a b) := by
    apply continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    rw [uIcc_of_le hab.le]
    intro t ht
    dsimp
    exact mul_ne_zero (by linarith [ht.1]) (by linarith [ht.2])
  simpa only [mul_one_div] using hcomp.mul_continuousOn hw

theorem lemma63_second_integrable {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    IntervalIntegrable (fun t =>
      f t * (Icc (a * c - 1) (b * c - 1)).indicator (fun _ => (1 : ℝ)) t / t *
        log ((1 - a) * (t + 1) / (a * (c - 1 - t)))) volume 1 3 := by
  have hg := source63_geometry ha hab hb hac hbc
  have hsub : uIcc (a * c - 1) (b * c - 1) ⊆ uIcc (1 : ℝ) 3 := by
    rw [uIcc_of_le (by linarith [hg.2.1]), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Icc_subset_Icc hg.2.2.2.1.1 hg.2.2.2.2.2
  have hl : ContinuousOn
      (fun t => log ((1 - a) * (t + 1) / (a * (c - 1 - t))))
      (uIcc (a * c - 1) (b * c - 1)) := by
    rw [uIcc_of_le (by linarith [hg.2.1])]
    apply ContinuousOn.log
    · exact (continuousOn_const.mul (continuousOn_id.add continuousOn_const)).div
        (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
        (fun t ht => by
          dsimp
          exact mul_ne_zero ha.ne' (by linarith [ht.2, hg.2.2.1]))
    · intro t ht
      dsimp
      exact ne_of_gt (div_pos (mul_pos (by linarith) (by linarith [ht.1]))
        (mul_pos ha (by linarith [ht.2, hg.2.2.1])))
  have hi := ((profile_div_integrable hf).mono_set hsub).mul_continuousOn hl
  have hind : Integrable ((Icc (a * c - 1) (b * c - 1)).indicator
      (fun t => f t / t * log ((1 - a) * (t + 1) / (a * (c - 1 - t))))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le
        (by linarith [hg.2.1] : a * c - 1 ≤ b * c - 1)).mp hi)
  convert hind.intervalIntegrable (a := 1) (b := 3) using 1
  ext t
  by_cases ht : t ∈ Icc (a * c - 1) (b * c - 1)
  · simp only [indicator_of_mem ht, mul_one]
  · simp only [indicator_of_notMem ht, mul_zero, zero_div, zero_mul]

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.source63_geometry
#check @WuPaper.RMapMSigma.source63_log_nonneg
#check @WuPaper.RMapMSigma.source63_partial_log_nonneg
#check @WuPaper.RMapMSigma.lemma63_lhs_integrable
#check @WuPaper.RMapMSigma.lemma63_second_integrable
#print axioms WuPaper.RMapMSigma.source63_geometry
#print axioms WuPaper.RMapMSigma.source63_log_nonneg
#print axioms WuPaper.RMapMSigma.source63_partial_log_nonneg
#print axioms WuPaper.RMapMSigma.lemma63_lhs_integrable
#print axioms WuPaper.RMapMSigma.lemma63_second_integrable
