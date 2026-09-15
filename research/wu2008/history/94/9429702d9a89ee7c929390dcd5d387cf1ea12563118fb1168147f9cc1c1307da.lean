import WRMapMMatrixGeometry

noncomputable section
namespace WuPaper.RMapMMatrix
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped Interval

private theorem reflected_affine_integral (g : ℝ → ℝ) (a b c S : ℝ) (hS : S ≠ 0) :
    (∫ u in a..b, S * g (c - S * u)) =
      ∫ v in (c - S * b)..(c - S * a), g v := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun v => g (c - v)) hS]
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hS, one_mul]
  exact intervalIntegral.integral_comp_sub_left g c

theorem source_fixed_inner_change (H : ℝ → ℝ) {S t a b : ℝ} (hS : S ≠ 0) :
    (∫ u in a..b, H (S * (1 - t - u)) / (u * (1 - t - u))) =
      ∫ v in (S * (1 - t - b))..(S * (1 - t - a)),
        S * H v / (v * (S - S * t - v)) := by
  let g := fun v => S * H v / (v * (S - S * t - v))
  have he (u : ℝ) :
      H (S * (1 - t - u)) / (u * (1 - t - u)) = S * g (S * (1 - t) - S * u) := by
    dsimp [g]
    rw [show S * (1 - t) - S * u = S * (1 - t - u) by ring,
      show S - S * t - S * (1 - t - u) = S * u by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = (S * S⁻¹) * (S * S⁻¹) *
          (H (S * (1 - t - u)) * ((1 - t - u)⁻¹ * u⁻¹)) := by
            rw [mul_inv_cancel₀ hS]
            ring
      _ = _ := by ring
  simp_rw [he]
  rw [reflected_affine_integral g a b (S * (1 - t)) S hS]
  convert rfl using 1
  congr 1 <;> ring

theorem source66_change_of_variables (H : ℝ → ℝ)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1 / p.S)..(1 / p.kappa2),
      (∫ u in t..(1 / p.kappa2),
        H (p.S - p.S * t - p.S * u) / (u * (1 - t - u))) / t) =
      ∫ t in (1 / p.S)..(1 / p.kappa2),
        (∫ v in (p.S * (1 - 1 / p.kappa2 - t))..(p.S * (1 - 2 * t)),
          p.S * H v / (v * (p.S - p.S * t - v))) / t := by
  have hS : p.S ≠ 0 := by have h := hp.2.2.1; linarith
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  congr 1
  simp_rw [show ∀ u, p.S - p.S * t - p.S * u = p.S * (1 - t - u) by
    intro u; ring]
  rw [source_fixed_inner_change H hS]
  congr 1 <;> ring

theorem source67_change_of_variables (H : ℝ → ℝ)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1 / p.S)..(1 / p.kappa1),
      (∫ u in (1 / p.kappa2)..(1 / p.kappa3),
        H (p.S - p.S * t - p.S * u) / (u * (1 - t - u))) / t) =
      ∫ t in (1 / p.S)..(1 / p.kappa1),
        (∫ v in (p.S * (1 - t - 1 / p.kappa3))..
          (p.S * (1 - t - 1 / p.kappa2)),
          p.S * H v / (v * (p.S - p.S * t - v))) / t := by
  have hS : p.S ≠ 0 := by have h := hp.2.2.1; linarith
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  congr 1
  simp_rw [show ∀ u, p.S - p.S * t - p.S * u = p.S * (1 - t - u) by
    intro u; ring]
  exact source_fixed_inner_change H hS

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.RMapMMatrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuPaper.RMapMMatrix
