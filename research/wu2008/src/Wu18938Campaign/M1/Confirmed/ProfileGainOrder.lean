import Wu18938Campaign.M1.Confirmed.ProfileFullLower

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval

theorem combinedUpper_le_classical {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {v : ℝ} (hv : 1 ≤ v) (hv5 : v ≤ 5) :
    combinedUpper H v ≤ wuUpperCoefficient v := by
  unfold combinedUpper
  split_ifs with hv3
  · have heq : wuUpperCoefficient v = 1 := jr1965F_normalized_initial (by linarith) hv3
    rw [heq]
    exact (min_le_left _ _).trans (upperInput_bounds
      (fun t ht => ⟨(hb t ht).1,(hb t ht).2.trans (by norm_num)⟩) v).2
  · rw [upperExtension_eq hH (le_of_not_ge hv3) hv5]
    have hn := (tailGain_bounds hH hb (aProfile_bounds hH hb).1 (le_of_not_ge hv3) hv5).1
    change 0 ≤ tailGain H (aProfile H) v at hn
    change wuUpperCoefficient v - tailGain H (aProfile H) v ≤ _
    linarith

theorem fullGain_integrable {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun v => (wuUpperCoefficient v - combinedUpper H v) / v) volume a b := by
  have hu : IntervalIntegrable (fun v => combinedUpper H v / v) volume a b := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using
      ((combinedUpper_mono hH hb).intervalIntegrable (μ := volume)).mul_continuousOn
        (reciprocal_continuous (by linarith) hab)
  simpa only [sub_div] using (wuUpperCoefficient_div_intervalIntegrable (by linarith) hab).sub hu

theorem fullLowerGain_nonneg {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {s : ℝ} (hs : 2 ≤ s) (hs6 : s ≤ 6) : 0 ≤ fullLowerGain H s := by
  apply intervalIntegral.integral_nonneg (by linarith : s - 1 ≤ 5)
  intro v hv
  exact div_nonneg (sub_nonneg.mpr (combinedUpper_le_classical hH hb (by linarith [hv.1]) hv.2))
    (by linarith [hv.1])

theorem fullLowerGain_antitone {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16) :
    AntitoneOn (fullLowerGain H) (Set.Icc 2 6) := by
  intro a ha b hb6 hab
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (fullGain_integrable hH hb (by linarith [ha.1] : 1 ≤ a - 1) (by linarith : a - 1 ≤ b - 1))
    (fullGain_integrable hH hb (by linarith [hb6.1] : 1 ≤ b - 1) (by linarith [hb6.2] : b - 1 ≤ 5))
  have hn : 0 ≤ ∫ v in (a - 1)..(b - 1), (wuUpperCoefficient v - combinedUpper H v) / v :=
    intervalIntegral.integral_nonneg (by linarith) (fun v hv =>
      div_nonneg (sub_nonneg.mpr (combinedUpper_le_classical hH hb
        (by linarith [ha.1,hv.1]) (by linarith [hb6.2,hv.2])))
        (by linarith [ha.1,hv.1]))
  unfold fullLowerGain
  linarith only [hs,hn]

theorem originalProfile_twentyone_nonneg {δ : ℝ} (n : ℕ) (j : Fin 21) :
    0 ≤ fullLowerGain (originalProfile δ n) (rNode (j.val + 1)) := by
  apply fullLowerGain_nonneg (originalProfile_antitone δ n) (fun v _ => originalProfile_bounds δ n v)
  · dsimp [rNode]; have hh := Nat.cast_nonneg (α := ℝ) (j.val + 1); linarith
  · exact (rNode_bounds (by omega : j.val + 1 ≤ 29)).2.trans (by norm_num)

end Wu18938Campaign.M1.Confirmed.FiniteProfile
