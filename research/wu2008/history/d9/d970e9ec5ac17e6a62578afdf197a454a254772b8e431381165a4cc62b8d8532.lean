import R2XiStripFubini

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem indicator_weight_integrable {f w : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hw : ContinuousOn w (Icc a b)) :
    IntervalIntegrable (fun t => f t * (Icc a b).indicator (fun _ => (1 : ℝ)) t * w t)
      volume 1 3 := by
  have hi : IntervalIntegrable (fun t => f t * w t) volume a b :=
    (hf.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      exact Icc_subset_Icc ha hb)).mul_continuousOn (by rwa [uIcc_of_le hab])
  have hind : Integrable ((Icc a b).indicator (fun t => f t * w t)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi)
  convert hind.intervalIntegrable (a := 1) (b := 3) using 1
  ext t
  by_cases ht : t ∈ Icc a b <;> simp [ht]

theorem source_log_domain {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    {t : ℝ} (ht : 1 ≤ t) (ht2 : t ≤ alpha2 p) :
    0 < t ∧ 0 < p.S - 1 - t ∧ 0 < 1 - t / p.S := by
  have hS := (second_parameter_bounds hp).2.1
  have hS0 : 0 < p.S := by linarith
  change t ≤ p.S - 2 at ht2
  refine ⟨by linarith, by linarith, ?_⟩
  have hdiv : t / p.S < 1 := (div_lt_one hS0).mpr (by linarith)
  linarith

theorem source_denominator_pos {S r t : ℝ} (hr : 0 < r)
    (ht : t < S - S / r) : 0 < r * S - S - r * t := by
  have hm := mul_pos hr (sub_pos.mpr ht)
  have hd := div_mul_cancel₀ S hr.ne'
  nlinarith

theorem K66_integrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    IntervalIntegrable (fun t => f t * K66 p t) volume 1 3 := by
  have ha := second_alpha_bounds hp
  have hb := second_parameter_bounds hp
  have hS0 : 0 < p.S := by linarith [hb.2.1]
  have hk2 : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have h64 := alpha6_le_alpha4 hk2 hb.2.2.2.2.2.2.2.1.le
  have h42 := ha.2.2.2.2.1
  have hi1 := indicator_weight_integrable hf (show 1 ≤ alpha6 p from (ha.1 5).1)
    h64 (show alpha4 p ≤ 3 from (ha.1 3).2) (w := fun t =>
      log (p.S / (p.kappa2 * p.S - p.S - p.kappa2 * t)) / (t * (1 - t / p.S))) (by
        intro t ht
        rcases source_log_domain hp ((ha.1 5).1.trans ht.1) (ht.2.trans h42) with ⟨ht0, hQ, hc⟩
        have hD := source_denominator_pos hk2 (by
          have h := ht.2
          dsimp [alpha4] at h
          linarith)
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  have hi2 := indicator_weight_integrable hf (show 1 ≤ alpha4 p from (ha.1 3).1)
    h42 (show alpha2 p ≤ 3 from (ha.1 1).2) (w := fun t =>
      log (p.S - 1 - t) / (t * (1 - t / p.S))) (by
        intro t ht
        rcases source_log_domain hp ((ha.1 3).1.trans ht.1) ht.2 with ⟨ht0, hQ, hc⟩
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  convert hi1.add hi2 using 1
  ext t
  dsimp [K66]
  ring

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
