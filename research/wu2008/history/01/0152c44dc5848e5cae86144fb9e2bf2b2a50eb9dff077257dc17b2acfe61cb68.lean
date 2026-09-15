import R2XiEquation68

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem remaining_piece_order {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    alpha7 p ≤ alpha5 p ∧ alpha9 p ≤ alpha1 p := by
  have hb := second_parameter_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk1 : 0 < p.kappa1 := by linarith [hb.2.2.2.1]
  have hk2 : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have h1S : p.kappa1 ≤ p.S := hp.2.2.2.2.2.2.2.1
  have h21 : p.kappa2 < p.kappa1 := hp.2.2.2.2.2.2.1
  have h := (one_le_div hk1).mpr h1S
  have h' := (one_le_div hk2).mpr h21.le
  dsimp [alpha7, alpha5, alpha9, alpha1]
  constructor <;> linarith

theorem source67_denominators {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    {t : ℝ} (ht : t ≤ alpha8 p) :
    0 < p.kappa1 * p.S - p.S - p.kappa1 * t := by
  have hb := second_parameter_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk1 : 0 < p.kappa1 := by linarith [hb.2.2.2.1]
  have hk2 : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  apply source_denominator_pos hk1
  dsimp [alpha8] at ht
  linarith [div_pos hS hk2]

theorem K67_integrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    IntervalIntegrable (fun t => f t * K67 p t) volume 1 3 := by
  have ha := second_alpha_bounds hp
  have hb := second_parameter_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk2 : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have hk3 : 0 < p.kappa3 := by linarith [hb.2.2.2.2.2.1]
  have h75 := (remaining_piece_order hp).1
  have h58 := ha.2.2.1.le
  have h84 := ha.2.2.2.2.2.2
  have h42 := ha.2.2.2.2.1
  have hi1 := indicator_weight_integrable hf (show 1 ≤ alpha7 p from (ha.1 6).1)
    h75 (show alpha5 p ≤ 3 from (ha.1 4).2) (w := fun t =>
      log (p.S ^ 2 / ((p.kappa1 * p.S - p.S - p.kappa1 * t) *
        (p.kappa3 * p.S - p.S - p.kappa3 * t))) / (t * (1 - t / p.S))) (by
        intro t ht
        rcases source_log_domain hp ((ha.1 6).1.trans ht.1) (ht.2.trans (h58.trans (h84.trans h42)))
          with ⟨ht0, hQ, hc⟩
        have hD1 := source67_denominators hp (ht.2.trans h58)
        have hD3 := source_denominator_pos (S := p.S) (t := t) hk3 (by
          have h := ht.2; dsimp [alpha5] at h; linarith)
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  have hi2 := indicator_weight_integrable hf (show 1 ≤ alpha5 p from (ha.1 4).1)
    h58 (show alpha8 p ≤ 3 from (ha.1 7).2) (w := fun t =>
      log (p.S * (p.S - 1 - t) / (p.kappa1 * p.S - p.S - p.kappa1 * t)) /
        (t * (1 - t / p.S))) (by
        intro t ht
        rcases source_log_domain hp ((ha.1 4).1.trans ht.1) (ht.2.trans (h84.trans h42))
          with ⟨ht0, hQ, hc⟩
        have hD1 := source67_denominators hp ht.2
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  have hi3 := indicator_weight_integrable hf (show 1 ≤ alpha8 p from (ha.1 7).1)
    h84 (show alpha4 p ≤ 3 from (ha.1 3).2) (w := fun t =>
      log ((p.S - 1 - t) * (p.kappa2 * p.S - p.S - p.kappa2 * t) / p.S) /
        (t * (1 - t / p.S))) (by
        intro t ht
        rcases source_log_domain hp ((ha.1 7).1.trans ht.1) (ht.2.trans h42)
          with ⟨ht0, hQ, hc⟩
        have hD2 := source_denominator_pos (S := p.S) (t := t) hk2 (by
          have h := ht.2; dsimp [alpha4] at h; linarith)
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  convert (hi1.add hi2).add hi3 using 1
  ext t
  dsimp [K67]
  ring

theorem K68_integrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    IntervalIntegrable (fun t => f t * K68 p t) volume 1 3 := by
  have ha := second_alpha_bounds hp
  have hb := second_parameter_bounds hp
  have hk2 : 0 < p.kappa2 - 1 := by linarith [hb.2.2.2.2.1]
  have h91 := (remaining_piece_order hp).2
  have h14 := ha.2.1.le
  have h42 := ha.2.2.2.2.1
  have hi1 := indicator_weight_integrable hf (show 1 ≤ alpha9 p from (ha.1 8).1)
    h91 (show alpha1 p ≤ 3 from (ha.1 0).2) (w := fun t =>
      log ((t + 1) / ((p.kappa2 - 1) * (p.kappa1 - 1 - t))) / t) (by
        intro t ht
        have ht0 : 0 < t := by linarith [(ha.1 8).1, ht.1]
        have hD : 0 < p.kappa1 - 1 - t := by
          have h := ht.2; dsimp [alpha1] at h; linarith
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  have hi2 := indicator_weight_integrable hf (show 1 ≤ alpha1 p from (ha.1 0).1)
    h14 (show alpha4 p ≤ 3 from (ha.1 3).2) (w := fun t =>
      log ((t + 1) / (p.kappa2 - 1)) / t) (by
        intro t ht
        have ht0 : 0 < t := by linarith [(ha.1 0).1, ht.1]
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity))
  have hi3 := indicator_weight_integrable hf (show 1 ≤ alpha4 p from (ha.1 3).1)
    h42 (show alpha2 p ≤ 3 from (ha.1 1).2) (w := fun t => log (p.S - 1 - t) / t) (by
      intro t ht
      rcases source_log_domain hp ((ha.1 3).1.trans ht.1) ht.2 with ⟨ht0, hQ, hc⟩
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity))
  convert (hi1.add hi2).add hi3 using 1
  ext t
  dsimp [K68]
  ring

theorem Xi2_integrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    IntervalIntegrable (fun t => f t * Xi2 p t) volume 1 3 :=
  (Xi2_integral_assembly hp (K65_integral_identity hf hp).1 (K66_integrable hf hp)
    (K67_integrable hf hp) (K68_integrable hf hp)).1

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
