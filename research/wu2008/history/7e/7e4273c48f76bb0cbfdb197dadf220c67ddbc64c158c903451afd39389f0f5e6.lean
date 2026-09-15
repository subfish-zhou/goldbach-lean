import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernel

/-!
# Sign and integrability of the literal closed-indicator kernel

Wu04 Proposition 3, author TeX lines 1246–1259. Each closed indicator is
handled independently, so shared endpoints and zero-length intervals
require no false pointwise partition identity.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem firstFeedbackXi_interval_endpoints {s t : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    1 ≤ t - t / s - 1 ∧ t - t / s - 1 ≤ t - 2 ∧ t - 2 ≤ 3 := by
  have hq : 1 ≤ t / s := (le_div_iff₀ (by linarith : 0 < s)).2 (by linarith)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem firstFeedbackXi_nonneg {x s t : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hx : x ∈ Icc (1 : ℝ) 3) :
    0 ≤ firstFeedbackXi x s t := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hs0 : 0 < s - 1 := by linarith
  have ht0 : 0 < t - 1 := by linarith
  have hp : 0 < (s - 1) * (t - 1) := mul_pos hs0 ht0
  unfold firstFeedbackXi
  apply add_nonneg
  · apply add_nonneg
    · apply mul_nonneg (div_nonneg (firstFeedbackSigmaZero_nonneg hx) (by positivity))
      apply Real.log_nonneg
      apply (le_div_iff₀ hp).2
      have hprod := mul_le_mul (show s - 1 ≤ 2 by linarith)
        (show t - 1 ≤ 4 by linarith) ht0.le (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    · by_cases hmem : x ∈ Icc (t - 2) 3
      · rw [indicator_of_mem hmem]
        apply mul_nonneg (by positivity)
        apply Real.log_nonneg
        apply (le_div_iff₀ hp).2
        have hst : s - 1 ≤ t - 1 := by linarith
        have hxt : t - 1 ≤ x + 1 := by linarith [hmem.1]
        have hprod := mul_le_mul hst hxt ht0.le (by linarith : 0 ≤ t - 1)
        nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1)
          (by linarith : 0 ≤ x + 1 - (t - 1))]
      · simp only [indicator_of_notMem hmem, zero_div, zero_mul, le_refl]
  · by_cases hmem : x ∈ Icc (t - t / s - 1) (t - 2)
    · rw [indicator_of_mem hmem]
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      have hd : 0 < t - 1 - x := by linarith [hmem.2]
      apply (le_div_iff₀ (mul_pos hs0 hd)).2
      have hq : t - (x + 1) ≤ t / s := by linarith [hmem.1]
      have hm := (le_div_iff₀ (by linarith : 0 < s)).mp hq
      nlinarith
    · simp only [indicator_of_notMem hmem, zero_div, zero_mul, le_refl]

theorem firstFeedbackXi_base_continuousOn (s t : ℝ) :
    ContinuousOn (fun x => firstFeedbackSigmaZero x / (2 * x) *
      log (16 / ((s - 1) * (t - 1)))) (Icc (1 : ℝ) 3) := by
  exact (firstFeedbackSigmaZero_continuousOn.div
    (continuousOn_const.mul continuousOn_id)
    (fun x hx => by change 2 * x ≠ 0; nlinarith [hx.1])).mul_const _

theorem firstFeedbackXi_tail_continuousOn {s t : ℝ}
    (hs : 1 < s) (ht : 1 < t) :
    ContinuousOn (fun x : ℝ => 1 / (2 * x) *
      log ((x + 1) ^ 2 / ((s - 1) * (t - 1)))) (Icc 1 3) := by
  have hd : (s - 1) * (t - 1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  apply ContinuousOn.mul
  · exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun x hx => by change 2 * x ≠ 0; nlinarith [hx.1])
  · apply ContinuousOn.log
    · exact ((continuousOn_id.add continuousOn_const).pow 2).div_const _
    · intro x hx
      exact div_ne_zero (pow_ne_zero 2 (by linarith [hx.1] : x + 1 ≠ 0)) hd

theorem firstFeedbackXi_middle_continuousOn {s t : ℝ}
    (hs : 1 < s) (hratio : 2 ≤ t - t / s) :
    ContinuousOn (fun x : ℝ => 1 / (2 * x) *
      log ((x + 1) / ((s - 1) * (t - 1 - x))))
      (Icc (t - t / s - 1) (t - 2)) := by
  have hx0 : ∀ x ∈ Icc (t - t / s - 1) (t - 2), 0 < x := by
    intro x hx
    linarith [hx.1]
  have hd : ∀ x ∈ Icc (t - t / s - 1) (t - 2),
      (s - 1) * (t - 1 - x) ≠ 0 := by
    intro x hx
    exact mul_ne_zero (by linarith) (by linarith [hx.2])
  apply ContinuousOn.mul
  · exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun x hx => mul_ne_zero (by norm_num) (hx0 x hx).ne')
  · apply ContinuousOn.log
    · exact (continuousOn_id.add continuousOn_const).div
        (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)) hd
    · intro x hx
      exact div_ne_zero (by linarith [hx0 x hx] : x + 1 ≠ 0) (hd x hx)

theorem firstFeedbackKernel_indicator_mul_intervalIntegrable
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume 1 3)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hg : ContinuousOn g (Icc a b)) :
    IntervalIntegrable (fun x => f x * (Icc a b).indicator (fun _ => (1 : ℝ)) x * g x)
      volume 1 3 := by
  have hsub : uIcc a b ⊆ uIcc (1 : ℝ) 3 := by
    rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact fun _ hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hfg : IntervalIntegrable (fun x => f x * g x) volume a b :=
    (hf.mono_set hsub).mul_continuousOn (by rwa [uIcc_of_le hab])
  have hi : IntegrableOn (fun x => f x * g x) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hfg
  have hj := ((integrable_indicator_iff measurableSet_Icc).mpr hi).intervalIntegrable
    (a := (1 : ℝ)) (b := 3)
  convert hj using 1
  ext x
  by_cases hx : x ∈ Icc a b
  · simp only [indicator_of_mem hx, mul_one]
  · simp only [indicator_of_notMem hx, mul_zero, zero_mul]

theorem firstFeedbackXi_mul_intervalIntegrable {f : ℝ → ℝ} {s t : ℝ}
    (hf : IntervalIntegrable f volume 1 3)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    IntervalIntegrable (fun x => f x * firstFeedbackXi x s t) volume 1 3 := by
  obtain ⟨ha, hab, hb⟩ := firstFeedbackXi_interval_endpoints hs hs3 ht ht5 hratio
  have hc : ContinuousOn (fun x => firstFeedbackSigmaZero x / (2 * x) *
      log (16 / ((s - 1) * (t - 1)))) (uIcc (1 : ℝ) 3) := by
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using
      firstFeedbackXi_base_continuousOn s t
  have hbase := hf.mul_continuousOn hc
  have htail := firstFeedbackKernel_indicator_mul_intervalIntegrable hf
    (by linarith : 1 ≤ t - 2) hb (by norm_num : (3 : ℝ) ≤ 3)
    ((firstFeedbackXi_tail_continuousOn (by linarith : 1 < s)
      (by linarith : 1 < t)).mono
      (fun _ hx => ⟨by linarith [hx.1], hx.2⟩))
  have hmid := firstFeedbackKernel_indicator_mul_intervalIntegrable hf ha hab hb
    (firstFeedbackXi_middle_continuousOn (by linarith) hratio)
  convert (hbase.add htail).add hmid using 1
  ext x
  dsimp [firstFeedbackXi]
  ring

theorem firstFeedbackXi_intervalIntegrable {s t : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    IntervalIntegrable (fun x => firstFeedbackXi x s t) volume 1 3 := by
  simpa only [one_mul] using firstFeedbackXi_mul_intervalIntegrable
    (f := fun _ => 1) intervalIntegrable_const hs hs3 ht ht5 hratio

theorem firstFeedbackXi_gain_intervalIntegrable (upper : Bool) {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    IntervalIntegrable (fun x => wuImprovementLimit upper δ x * firstFeedbackXi x s t)
      volume 1 3 :=
  firstFeedbackXi_mul_intervalIntegrable
    (wuImprovementLimit_intervalIntegrable upper hδ hδhi
      (by norm_num) (by norm_num) (by norm_num)) hs hs3 ht ht5 hratio

end Wu2008DoubleSieve
