import Wu18938Campaign.M1.Confirmed.ProfileExtension

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval

def tailGain (H : ℝ → ℝ) (c v : ℝ) : ℝ :=
  c * log (4 / (v - 1)) +
    ∫ t in (v - 2)..3, H t / t * log ((t + 1) / (v - 1))

theorem logMoment_integrable {H : ℝ → ℝ} (hH : Antitone H)
    {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    IntervalIntegrable (fun t => H t / t * log ((t + 1) / (v - 1)))
      volume (v - 2) 3 :=
  (profile_subinterval (profile_div_integrable hH.intervalIntegrable)
    (by linarith) (by linarith)).mul_continuousOn (log_weight_continuous hv hv5)

theorem tailGain_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {c v : ℝ} (hc : 0 ≤ c) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    0 ≤ tailGain H c v ∧ tailGain H c v ≤ c + 1 / 8 := by
  have hL0 : 0 ≤ log (4 / (v - 1)) :=
    log_nonneg ((le_div_iff₀ (by linarith : 0 < v - 1)).mpr (by linarith))
  have hL1 : log (4 / (v - 1)) ≤ 1 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hm := log_le_log (div_pos (by norm_num) (by linarith : 0 < v - 1))
      ((div_le_iff₀ (by linarith : 0 < v - 1)).mpr (by linarith : (4 : ℝ) ≤ 2 * (v - 1)))
    linarith
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (v - 2) 3) :
      0 ≤ H t / t * log ((t + 1) / (v - 1)) ∧
      H t / t * log ((t + 1) / (v - 1)) ≤ 1 / 16 := by
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hh := hb t ⟨ht1,ht.2⟩
    have hq0 : 0 ≤ H t / t := div_nonneg hh.1 (by linarith)
    have hq : H t / t ≤ 1 / 16 :=
      (div_le_iff₀ (by linarith : 0 < t)).mpr (by linarith [hh.2])
    have hl0 : 0 ≤ log ((t + 1) / (v - 1)) :=
      log_nonneg ((le_div_iff₀ (by linarith : 0 < v - 1)).mpr (by linarith [ht.1]))
    have hl1 : log ((t + 1) / (v - 1)) ≤ 1 :=
      (log_le_log (div_pos (by linarith) (by linarith))
        (div_le_div_of_nonneg_right (by linarith [ht.2]) (by linarith))).trans hL1
    exact ⟨mul_nonneg hq0 hl0,(mul_le_mul hq hl1 hl0 (by norm_num)).trans_eq (mul_one _)⟩
  have hi := logMoment_integrable hH hv hv5
  have hnonneg := intervalIntegral.integral_nonneg (μ := volume)
    (by linarith : v - 2 ≤ 3) (fun t ht => (hpoint t ht).1)
  have hbound := intervalIntegral.integral_mono_on (by linarith : v - 2 ≤ 3) hi
    (intervalIntegrable_const (c := (1 / 16 : ℝ))) (fun t ht => (hpoint t ht).2)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hbound
  have hprod := mul_le_mul_of_nonneg_left hL1 hc
  dsimp [tailGain]
  constructor
  · exact add_nonneg (mul_nonneg hc hL0) hnonneg
  · nlinarith

theorem upperExtension_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {c : ℝ} (hc : 0 ≤ c) (hc4 : c ≤ 1 / 4) (v : ℝ) :
    0 ≤ upperExtension H c v ∧ upperExtension H c v ≤ 10 := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  let x := max 3 (min v 5)
  have hx : 3 ≤ x := le_max_left _ _
  have hx5 : x ≤ 5 := max_le (by norm_num) (min_le_right _ _)
  have heq : upperExtension H c v = upperExtension H c x := by
    simp only [upperExtension,min_eq_left hx5,max_eq_right hx]
    rfl
  have hmin : 0 ≤ upperExtension H c 3 := by
    rw [upperExtension_eq hH (by norm_num : (3 : ℝ) ≤ 3) (by norm_num)]
    have ha : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
    rw [ha]
    have hh := (tailGain_bounds hH hb hc (v := 3) (by norm_num) (by norm_num)).2
    change 0 ≤ 1 - tailGain H c 3
    linarith
  have hu : wuUpperCoefficient 5 ≤ 10 := by
    unfold wuUpperCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).mpr
    have hh := jr1965F_le_delayConstant (u := 5) (by norm_num)
    unfold jr1965DelayConstant at hh
    nlinarith [exp_pos eulerMascheroniConstant]
  have hi : 0 ≤ profileIntegral (lowerExtension H c) x 5 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t ht =>
      div_nonneg (lowerExtension_bounds hH hb1 hc t).1 (by linarith [ht.1]))
  refine ⟨?_,?_⟩
  · rw [heq]
    exact hmin.trans (upperExtension_mono hH hb1 hc hx)
  · change wuUpperCoefficient 5 - profileIntegral (lowerExtension H c) x 5 ≤ 10
    linarith

theorem sigma0_le_two {t : ℝ} (ht : t ∈ Set.Icc (1 : ℝ) 3) : sigma0 t ≤ 2 := by
  have hab : 3 ≤ t + 2 := by linarith [ht.1]
  have hi := sigma_integrable (a := 3) (b := t + 2) (c := t + 1)
    (by norm_num) hab (by linarith [ht.1])
  have hh := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (1 / 3 : ℝ))) (fun v hv => by
      have hp : 0 < v - 1 := by linarith [hv.1]
      have hL : log ((t + 1) / (v - 1)) ≤ 1 := by
        have hm := log_le_log (div_pos (by linarith [ht.1]) hp)
          ((div_le_iff₀ hp).mpr (by linarith [ht.2,hv.1] : t + 1 ≤ 2 * (v - 1)))
        linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (div_le_iff₀ (by linarith [hv.1] : 0 < v)).mpr (by linarith [hv.1]))
  rw [intervalIntegral.integral_const,smul_eq_mul] at hh
  unfold sigma0
  apply (div_le_iff₀ (sub_pos.mpr D0_lt_one)).mpr
  change sigma 3 (t + 2) (t + 1) ≤ _ at hh
  linarith [ht.2,D0_bounds.2]

theorem aProfile_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16) :
    0 ≤ aProfile H ∧ aProfile H ≤ 1 / 4 := by
  have hn := (profiles_nonneg (fun v hv => (hb v hv).1)).1
  have hs := sigma_feedback (profile_div_integrable hH.intervalIntegrable)
  have hh := intervalIntegral.integral_mono_on (by norm_num : (3 : ℝ) ≤ 5) hs.1
    (intervalIntegrable_const (c := (1 / 24 : ℝ))) (fun v hv => by
      have hm := (tailGain_bounds hH hb (c := 0) (by norm_num) hv.1 hv.2).2
      simp only [tailGain,zero_mul,zero_add] at hm
      apply (div_le_iff₀ (by linarith [hv.1] : 0 < v)).mpr
      linarith [hv.1])
  norm_num only [intervalIntegral.integral_const,smul_eq_mul] at hh
  refine ⟨hn,?_⟩
  rw [aProfile_eq,← hs.2]
  apply (div_le_iff₀ (sub_pos.mpr D0_lt_one)).mpr
  linarith [D0_bounds.2]

end Wu18938Campaign.M1.Confirmed.FiniteProfile
