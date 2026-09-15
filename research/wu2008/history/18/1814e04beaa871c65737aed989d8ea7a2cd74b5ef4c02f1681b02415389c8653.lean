import RMapMDebitFormulas

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuPaper.RMapMDebit

theorem seventh_change_of_variables :
    (∫ y in (2 : ℝ)..(2 / (1 - 6 * alpha) - 1), log (y - 1) / y) =
      SeventhEighth.J7 := by
  have hs0 : 0 < sigma := lt_trans (by norm_num) parameters.2.2.2.2.1
  have hs3 : sigma ≤ (1 / 3 : ℝ) := parameters.2.2.2.2.2.1.le
  have hx (x : ℝ) (hx : x ∈ uIcc sigma (1 / 3 : ℝ)) :
      0 < x ∧ x ≤ 1 / 3 := by
    rw [uIcc_of_le hs3] at hx
    exact ⟨hs0.trans_le hx.1, hx.2⟩
  have hd (x : ℝ) (h : x ∈ uIcc sigma (1 / 3 : ℝ)) :
      HasDerivAt (fun x : ℝ => 1 / x - 1) (-1 / x^2) x := by
    convert (((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x)
      (hx x h).1.ne').sub_const 1) using 1 <;>
      first | rfl | (dsimp; ring)
  have hc : ContinuousOn (fun x : ℝ => -1 / x^2) (uIcc sigma (1 / 3)) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun x h => pow_ne_zero 2 (hx x h).1.ne')
  have hy (y : ℝ)
      (h : y ∈ (fun x : ℝ => 1 / x - 1) '' uIcc sigma (1 / 3)) : 2 ≤ y := by
    obtain ⟨x, h, rfl⟩ := h
    have hh := (le_div_iff₀ (hx x h).1).2
      (show (3 : ℝ) * x ≤ 1 by linarith [(hx x h).2])
    linarith only [hh]
  have hg : ContinuousOn (fun y : ℝ => log (y - 1) / y)
      ((fun x : ℝ => 1 / x - 1) '' uIcc sigma (1 / 3)) :=
    ((continuousOn_id.sub continuousOn_const).log
      (fun y h => (show 0 < y - 1 by linarith [hy y h]).ne')).div continuousOn_id
      (fun y h => (show 0 < y by linarith [hy y h]).ne')
  have he := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  have hkernel :
      (∫ x in sigma..(1 / 3 : ℝ),
        ((fun y : ℝ => log (y - 1) / y) ∘ (fun x : ℝ => 1 / x - 1)) x *
          (-1 / x^2)) = -SeventhEighth.J7 := by
    unfold SeventhEighth.J7
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x h
    have hx0 := (hx x h).1
    have hx1 : 0 < 1 - x := by linarith [(hx x h).2]
    dsimp [Function.comp_def]
    rw [show 1 / x - 1 - 1 = (1 - 2 * x) / x by field_simp; ring,
      show 1 / x - 1 = (1 - x) / x by field_simp]
    field_simp
  rw [hkernel] at he
  have he3 : 1 / (1 / 3 : ℝ) - 1 = 2 := by norm_num
  rw [he3, seventh_endpoint, intervalIntegral.integral_symm] at he
  linarith only [he]

theorem C7_eq_existing : C7 = Wu08TerminalAlignment.seventhMain := by
  unfold C7 Wu08TerminalAlignment.seventhMain
  rw [seventh_change_of_variables]

theorem C9_integrable :
    IntervalIntegrable (fun t : ℝ =>
      log ((1 + 6 * alpha - 2 * t) / (1 - 6 * alpha)) / (t * (1 - t)))
      volume beta sigma := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le parameters.2.2.2.1.le]
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).div_const _
    · exact fun t ht => (lt_trans (by norm_num) (ninth_domain ht).2.2).ne'
  · fun_prop
  · exact fun t ht => mul_ne_zero (ninth_domain ht).1.ne' (ninth_domain ht).2.1.ne'

theorem C7_nonneg : 0 ≤ C7 := by
  rw [C7_eq_existing]
  exact mul_nonneg (by norm_num) SeventhEighth.J7_nonneg

theorem C8_nonneg : 0 ≤ C8 := by
  unfold C8
  have hs : 0 ≤ ∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t)^2) := by
    apply intervalIntegral.integral_nonneg parameters.2.1.le
    intro t ht
    have h := eighth_domain (show t ∈ Icc alpha (1 / 3 : ℝ) from
      ⟨ht.1, ht.2.trans (by norm_num)⟩)
    exact div_nonneg (log_nonneg h.2.2) (mul_nonneg h.1.le (sq_nonneg _))
  have hl : 0 ≤ ∫ t in (1 / 10 : ℝ)..(1 / 3),
      log (2 - 3 * t) / (t * (1 - t)) := by
    apply intervalIntegral.integral_nonneg (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)
    intro t ht
    have h := eighth_domain (show t ∈ Icc alpha (1 / 3 : ℝ) from
      ⟨parameters.2.1.le.trans ht.1, ht.2⟩)
    exact div_nonneg (log_nonneg h.2.2) (mul_nonneg h.1.le h.2.1.le)
  positivity

theorem C9_nonneg : 0 ≤ C9 := by
  unfold C9
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg parameters.2.2.2.1.le
  intro t ht
  have h := ninth_domain ht
  exact div_nonneg (log_nonneg h.2.2.le) (mul_nonneg h.1.le h.2.1.le)

theorem weighted_original_identity :
    2 * C7 + C8 + C9 = WuTarget.W12.weightedDebit := by
  rw [C7_eq_existing, C8_eq_existing, C9_eq_existing]
  rfl

theorem existing_correction_once :
    2 * C7 + C8 + C9 =
      16 * SeventhEighth.J7 + 8 * SeventhEighth.J8 + 8 * J9 -
        8 * (U8CanonicalMother.L - U8CanonicalMother.I) := by
  rw [C7_eq_existing, C8_eq_existing, C9_eq_existing]
  unfold Wu08TerminalAlignment.seventhMain Wu08TerminalAlignment.eighthMain
    Wu08TerminalAlignment.ninthMain
  ring

end WuPaper.RMapMDebit
