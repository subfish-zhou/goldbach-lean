import R2XiEquation66

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem fixed_cut_upper {S r q v : ℝ} (hS : 0 < S) :
    v ≤ S * (1 - r - q) ↔ r + q ≤ 1 - v / S := by
  rw [mul_comm S, ← div_le_iff₀ hS]
  constructor <;> intro h <;> linarith

theorem fixed_cut_lower {S r q v : ℝ} (hS : 0 < S) :
    S * (1 - r - q) ≤ v ↔ 1 - v / S ≤ r + q := by
  rw [mul_comm S, ← le_div_iff₀ hS]
  constructor <;> intro h <;> linarith

theorem fixed_rectangle_section_iff {S d e x v : ℝ} (hS : 0 < S) :
    v ∈ Icc (S * (1 - e - x)) (S * (1 - d - x)) ↔
      x ∈ Icc (1 - v / S - e) (1 - v / S - d) := by
  simp only [mem_Icc, fixed_cut_lower hS, fixed_cut_upper hS]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem source67_endpoint_identities {p : SecondFunctionalParameters}
    (hp : PropositionFourGeometry p) :
    alpha7 p = p.S * (1 - 1 / p.kappa3 - 1 / p.kappa1) ∧
    alpha5 p = p.S * (1 - 1 / p.kappa3 - 1 / p.S) ∧
    alpha8 p = p.S * (1 - 1 / p.kappa2 - 1 / p.kappa1) ∧
    alpha4 p = p.S * (1 - 1 / p.kappa2 - 1 / p.S) := by
  have hS : p.S ≠ 0 := by linarith [(second_parameter_bounds hp).2.1]
  refine ⟨by dsimp [alpha7]; ring, ?_, by dsimp [alpha8]; ring, ?_⟩
  · dsimp [alpha5]
    field_simp
  · dsimp [alpha4]
    field_simp

theorem source67_strip_bounds {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    ∀ x ∈ Icc (1 / p.S) (1 / p.kappa1),
      1 ≤ p.S * (1 - 1 / p.kappa3 - x) ∧
      p.S * (1 - 1 / p.kappa3 - x) ≤ p.S * (1 - 1 / p.kappa2 - x) ∧
      p.S * (1 - 1 / p.kappa2 - x) ≤ 3 := by
  have hb := second_parameter_bounds hp
  have ha := (second_alpha_bounds hp).1
  rcases hp with ⟨_, _, _, _, _, h32, _, _, _⟩
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk3 : 0 < p.kappa3 := by linarith [hb.2.2.2.2.2.1]
  have hdiv := one_div_le_one_div_of_le hk3 h32.le
  intro x hx
  have hlo := mul_le_mul_of_nonneg_left hx.1 hS.le
  have hhi := mul_le_mul_of_nonneg_left hx.2 hS.le
  have hm := mul_le_mul_of_nonneg_left hdiv hS.le
  simp only [mul_one_div, div_self hS.ne'] at hlo hhi hm
  have h7 : 1 ≤ p.S - p.S / p.kappa1 - p.S / p.kappa3 := (ha 6).1
  have h4 : p.S - p.S / p.kappa2 - 1 ≤ 3 := (ha 3).2
  simp only [div_eq_mul_inv] at *
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem source67_fubini {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ x in (1 / p.S)..(1 / p.kappa1),
      (∫ v in (p.S * (1 - x - 1 / p.kappa3))..(p.S * (1 - x - 1 / p.kappa2)),
        p.S * f v / (v * (p.S - p.S * x - v))) / x) =
      ∫ v in (1 : ℝ)..3, ∫ x in (1 / p.S)..(1 / p.kappa1),
        (Icc (p.S * (1 - 1 / p.kappa3 - x)) (p.S * (1 - 1 / p.kappa2 - x))).indicator
          (fun v => (p.S * f v / (v * (p.S - p.S * x - v))) / x) v := by
  have hb := second_parameter_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk1 : 0 < p.kappa1 := by linarith [hb.2.2.2.1]
  have hk2 : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have hkS : p.kappa1 ≤ p.S := hp.2.2.2.2.2.2.2.1
  have hab := one_div_le_one_div_of_le hk1 hkS
  have hbounds := source67_strip_bounds hp
  have hi := strip_profile_integrable hab (by norm_num : (1 : ℝ) ≤ 3) hf
    (l := fun x => p.S * (1 - 1 / p.kappa3 - x))
    (u := fun x => p.S * (1 - 1 / p.kappa2 - x))
    (by fun_prop) (by fun_prop) hbounds
    (w := fun z => p.S / (z.2 * (p.S - p.S * z.1 - z.2)) / z.1) (by
      intro z hz
      have hx0 : 0 < z.1 := (one_div_pos.mpr hS).trans_le hz.1.1
      have hv0 : 0 < z.2 := by linarith [(hbounds z.1 hz.1).1, hz.2.1]
      have hden : 0 < p.S - p.S * z.1 - z.2 := by
        have hpos := mul_pos hS (one_div_pos.mpr hk2)
        nlinarith [hz.2.2]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity))
  have hi' : IntegrableOn (fun z : ℝ × ℝ =>
      (p.S * f z.2 / (z.2 * (p.S - p.S * z.1 - z.2))) / z.1)
      (strip (1 / p.S) (1 / p.kappa1)
        (fun x => p.S * (1 - 1 / p.kappa3 - x)) (fun x => p.S * (1 - 1 / p.kappa2 - x))) := by
    convert hi using 1
    ext z
    ring
  have hswap := strip_fubini hab (by norm_num : (1 : ℝ) ≤ 3)
    (by fun_prop) (by fun_prop) hbounds hi'
  simp only [intervalIntegral.integral_div] at hswap
  convert hswap using 1
  congr 1
  ext x
  congr 2 <;> ring

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
