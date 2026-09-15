import WSrcNineRows

noncomputable section
namespace WuSource.SrcNine
open Wu2008DoubleSieve ActualNineFeedback NodeExtension

def zQ : Fin 9 → ℚ :=
  ![18803317/1000000000, 18187144/1000000000, 16806736/1000000000,
    15160322/1000000000, 13933425/1000000000, 11221052/1000000000,
    8434404/1000000000, 6314864/1000000000, 5909403/1000000000]

theorem z_eq_cast (i : Fin 9) : z i = (zQ i : ℝ) := by
  fin_cases i <;> norm_num [z, zQ]

theorem z_positive (i : Fin 9) : 0 < z i := by
  fin_cases i <;> norm_num [z]

theorem z_stronger_than_seed (i : Fin 9) : WuTarget.W09.seed i < z i := by
  fin_cases i <;> norm_num [z, WuTarget.W09.seed, WuTarget.W09.seedQ]

theorem actual_nine_lower {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ d) (i : Fin 9) :
    z i ≤ actualNine δ i :=
  certified_lower_subsolution z_nonneg all_rows hδ hr i

theorem actual_H_lower {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ d) (i : Fin 9) :
    z i ≤ wuImprovementLimit true δ ((22 + (i.val : ℝ)) / 10) :=
  actual_nine_lower hδ hr i

theorem explicit_certificate :
    0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) d, ∀ i : Fin 9, z i ≤ actualNine δ i :=
  ⟨d_pos, d_cap, fun _ hδ i => actual_nine_lower hδ.1 hδ.2 i⟩

theorem preferred_target_not_met (i : Fin 9) :
    z i < NineFeedbackStrength.originalH i - 1 / 10000 := by
  fin_cases i <;> norm_num [z, NineFeedbackStrength.originalH]

theorem exact_target_deficits (i : Fin 9) :
    NineFeedbackStrength.originalH i - z i =
      (![3590583/1000000000, 3532456/1000000000, 3480864/1000000000,
        2982978/1000000000, 1930975/1000000000, 1771248/1000000000,
        1634196/1000000000, 1501336/1000000000, 1384897/1000000000] :
        Fin 9 → ℝ) i := by
  fin_cases i <;> norm_num [z, NineFeedbackStrength.originalH]

theorem certified_uniform_target_error (i : Fin 9) :
    NineFeedbackStrength.originalH i - 3590583 / 1000000000 ≤ z i := by
  fin_cases i <;> norm_num [z, NineFeedbackStrength.originalH]

theorem actual_H_with_uniform_target_error {δ : ℝ}
    (hδ : 0 < δ) (hr : δ ≤ d) (i : Fin 9) :
    NineFeedbackStrength.originalH i - 3590583 / 1000000000 ≤
      wuImprovementLimit true δ ((22 + (i.val : ℝ)) / 10) :=
  (certified_uniform_target_error i).trans (actual_H_lower hδ hr i)

end WuSource.SrcNine
