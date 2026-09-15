import RMapMMatrixSubstitution

noncomputable section
namespace WuPaper.RMapMMatrix
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped Interval

theorem source_selected_inner_change (H : ℝ → ℝ) {t a b : ℝ} (ht : t ≠ 0) :
    (∫ u in a..b, H ((1 - t - u) / t) / (u * (1 - t - u))) =
      ∫ v in ((1 - t - b) / t)..((1 - t - a) / t),
        H v / (v * (1 - t - v * t)) := by
  have he (v : ℝ) :
      (1 / t) * H v / (v * (1 / t - (1 / t) * t - v)) =
        H v / (v * (1 - t - v * t)) := by
    rw [show 1 / t - (1 / t) * t - v = (1 - t - v * t) / t by
      field_simp; ring]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_inv]
    calc
      _ = (t⁻¹ * t) * (H v * ((1 - t - v * t)⁻¹ * v⁻¹)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ ht, one_mul]
  have h := source_fixed_inner_change H (S := 1 / t) (t := t)
    (a := a) (b := b) (one_div_ne_zero ht)
  simp_rw [he, show ∀ x : ℝ, (1 / t) * (1 - t - x) = (1 - t - x) / t by
    intro x; ring] at h
  exact h

theorem source68_change_of_variables (H : ℝ → ℝ)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1 / p.S)..(1 / p.kappa1),
      (∫ u in t..(1 / p.kappa2),
        H ((1 - t - u) / t) / (u * (1 - t - u))) / t) =
      ∫ t in (1 / p.S)..(1 / p.kappa1),
        (∫ v in ((1 - t - 1 / p.kappa2) / t)..(1 / t - 2),
          H v / (v * (1 - t - v * t))) / t := by
  rcases hp with ⟨hs, _, hS, _, hs3, h32, h21, h1S, _⟩
  have hS0 : 0 < p.S := by linarith
  have hk10 : 0 < p.kappa1 := by linarith
  have hab : 1 / p.S ≤ 1 / p.kappa1 :=
    one_div_le_one_div_of_le hk10 h1S
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := ne_of_gt ((one_div_pos.mpr hS0).trans_le ht.1)
  dsimp only
  rw [source_selected_inner_change H ht0]
  rw [show (1 - t - t) / t = 1 / t - 2 by field_simp; ring]

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.RMapMMatrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuPaper.RMapMMatrix
