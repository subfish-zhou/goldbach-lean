import W12WeightedDebit

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuPaper.RMapMDebit

abbrev alpha : ℝ := SeventhEighth.alpha
abbrev beta : ℝ := SeventhEighth.beta
abbrev sigma : ℝ := SeventhEighth.sigma

def C7 : ℝ :=
  8 * ∫ t in (2 : ℝ)..(2 / (1 - 6 * alpha) - 1), log (t - 1) / t

def C8 : ℝ :=
  (36 / 5) * (∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t)^2)) +
    8 * (∫ t in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * t) / (t * (1 - t)))

def C9 : ℝ :=
  8 * ∫ t in beta..sigma,
    log ((1 + 6 * alpha - 2 * t) / (1 - 6 * alpha)) / (t * (1 - t))

theorem parameters :
    0 < alpha ∧ alpha < 1 / 10 ∧ 1 / 10 < beta ∧ beta < sigma ∧
      1 / 4 < sigma ∧ sigma < 1 / 3 ∧ 0 < 1 - 6 * alpha := by
  norm_num [alpha, beta, sigma, SeventhEighth.alpha, SeventhEighth.beta,
    SeventhEighth.sigma]

theorem wu04_eighth_condition : 1 < 3 * (1 / 3 : ℝ) + alpha := by
  linarith [parameters.1]

theorem wu04_ninth_condition : 1 < 2 * (1 / 3 : ℝ) + sigma + beta := by
  norm_num [beta, sigma, SeventhEighth.beta, SeventhEighth.sigma, SeventhEighth.alpha]

theorem seventh_endpoint : 1 / sigma - 1 = 2 / (1 - 6 * alpha) - 1 := by
  norm_num [sigma, alpha, SeventhEighth.sigma, SeventhEighth.alpha]

theorem eighth_log_argument (t : ℝ) :
    1 / (1 / 3 : ℝ) - 1 - t / (1 / 3) = 2 - 3 * t := by ring

theorem ninth_log_argument (t : ℝ) :
    (1 - sigma - t) / sigma =
      (1 + 6 * alpha - 2 * t) / (1 - 6 * alpha) := by
  norm_num [sigma, alpha, SeventhEighth.sigma, SeventhEighth.alpha]
  ring

theorem eighth_domain {t : ℝ} (ht : t ∈ Icc alpha (1 / 3 : ℝ)) :
    0 < t ∧ 0 < 1 - t ∧ 1 ≤ 2 - 3 * t := by
  exact ⟨parameters.1.trans_le ht.1, by linarith [ht.2], by linarith [ht.2]⟩

theorem ninth_domain {t : ℝ} (ht : t ∈ Icc beta sigma) :
    0 < t ∧ 0 < 1 - t ∧
      1 < (1 + 6 * alpha - 2 * t) / (1 - 6 * alpha) := by
  have hs : sigma < (1 / 3 : ℝ) := parameters.2.2.2.2.2.1
  have hb : 0 < beta := lt_trans (by norm_num) parameters.2.2.1
  refine ⟨hb.trans_le ht.1, by linarith [ht.2], ?_⟩
  rw [← ninth_log_argument]
  apply (lt_div_iff₀ (lt_trans (by norm_num) parameters.2.2.2.2.1)).2
  linarith [ht.2]

theorem seventh_domain {t : ℝ}
    (ht : t ∈ Icc (2 : ℝ) (2 / (1 - 6 * alpha) - 1)) :
    0 < t ∧ 1 ≤ t - 1 := by
  constructor <;> linarith [ht.1]

theorem C7_integrable :
    IntervalIntegrable (fun t : ℝ => log (t - 1) / t) volume
      2 (2 / (1 - 6 * alpha) - 1) := by
  have hab : (2 : ℝ) ≤ 2 / (1 - 6 * alpha) - 1 := by
    norm_num [alpha, SeventhEighth.alpha]
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · exact (continuousOn_id.sub continuousOn_const).log
      (fun t ht => (lt_of_lt_of_le (by norm_num) (seventh_domain ht).2).ne')
  · exact continuousOn_id
  · exact fun t ht => (seventh_domain ht).1.ne'

theorem C8_small_integrable :
    IntervalIntegrable (fun t : ℝ => log (2 - 3 * t) / (t * (1 - t)^2))
      volume alpha (1 / 10) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le parameters.2.1.le]
  have hd (t : ℝ) (ht : t ∈ Icc alpha (1 / 10 : ℝ)) :=
    eighth_domain (show t ∈ Icc alpha (1 / 3 : ℝ) from
      ⟨ht.1, ht.2.trans (by norm_num)⟩)
  apply ContinuousOn.div
  · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
      (fun t ht => (lt_of_lt_of_le (by norm_num) (hd t ht).2.2).ne')
  · fun_prop
  · exact fun t ht => mul_ne_zero (hd t ht).1.ne' (pow_ne_zero 2 (hd t ht).2.1.ne')

theorem C8_split :
    SeventhEighth.J8 =
      (∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t))) +
      (∫ t in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * t) / (t * (1 - t))) := by
  have hi := SeventhEighth.J8_integrable
  have hleft : IntervalIntegrable (fun t : ℝ => log (2 - 3 * t) / (t * (1 - t)))
      volume alpha (1 / 10) := hi.mono_set (by
    rw [uIcc_of_le parameters.2.1.le, uIcc_of_le
      (parameters.2.1.le.trans (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3))]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have hright : IntervalIntegrable (fun t : ℝ => log (2 - 3 * t) / (t * (1 - t)))
      volume (1 / 10) (1 / 3) := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3), uIcc_of_le
      (parameters.2.1.le.trans (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3))]
    exact Icc_subset_Icc parameters.2.1.le le_rfl)
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

theorem C8_eq_existing : C8 = Wu08TerminalAlignment.eighthMain := by
  unfold C8 Wu08TerminalAlignment.eighthMain
  rw [C8_split, U8CanonicalMother.L_literal, U8CanonicalMother.I_literal]
  change (36 / 5) * (∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t)^2)) +
      8 * (∫ t in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * t) / (t * (1 - t))) =
    8 * ((∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t))) +
      (∫ t in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * t) / (t * (1 - t)))) -
      8 * ((∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t))) -
        (9 / 10) * (∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t)^2)))
  ring

theorem C9_eq_existing : C9 = Wu08TerminalAlignment.ninthMain := by
  unfold C9 Wu08TerminalAlignment.ninthMain J9
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change log ((1 + 6 * alpha - 2 * t) / (1 - 6 * alpha)) / (t * (1 - t)) =
    log ((1 - sigma - t) / sigma) / (t * (1 - t))
  rw [ninth_log_argument]

end WuPaper.RMapMDebit
