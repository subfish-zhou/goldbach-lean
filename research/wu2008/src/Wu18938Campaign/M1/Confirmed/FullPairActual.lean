import Wu18938Campaign.M1.Confirmed.PairLiteralKernel
import Wu18938Campaign.M1.Confirmed.OriginalProfileIteration
import WR2Gamma5Original

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Real NodeExtension ActualNineFeedback
open scoped Classical

theorem originalProfile_gamma5 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (j : Fin 4) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      secondFunctionalMotherGammaSum (coupledRow j) N δ (convolutionWuWindows N Δ V) 5 ≤
        (Pair.classicalIntegral (coupledRow j) .gammaFive -
          WuPaper.R2Xi.original66 (FiniteProfile.originalProfile δ n) (coupledRow j) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hh := profile_actual (coupledRow j) (WuPaper.R2Gamma5.original_full_parameters j)
    (FiniteProfile.originalProfile δ n) (FiniteProfile.originalProfile_antitone δ n)
    (fun v _ => ⟨(FiniteProfile.originalProfile_bounds δ n v).1,
      (FiniteProfile.originalProfile_bounds δ n v).2.trans (by norm_num)⟩)
    hδ (FiniteProfile.originalProfile_actual hδ hδhi n) m hη he
  rw [PairLiteral.five_original66 (coupledRow_geometry j).1
    (FiniteProfile.originalProfile_antitone δ n).measurable (by
      intro v
      rw [abs_of_nonneg (FiniteProfile.originalProfile_bounds δ n v).1]
      exact (FiniteProfile.originalProfile_bounds δ n v).2.trans (by norm_num))] at hh
  exact hh

theorem original_fullH (j : Fin 4) : FullHParameters (coupledRow j) := by
  fin_cases j
  · exact row1_fullH
  · exact row2_fullH
  · exact row3_fullH
  · exact row4_fullH

theorem all_pair_actual (j : Fin 4) (H : ℝ → ℝ) (hm : Antitone H)
    (hH : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hn : FiniteProfile.UpperNodes δ (fun v => 1 - H v) 3)
    (k : Term) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      secondFunctionalMotherGammaSum (coupledRow j) N δ (convolutionWuWindows N Δ V) k.index ≤
        (Pair.classicalIntegral (coupledRow j) k -
          (∫ v : ℝ × ℝ, PairLiteral.kernel (coupledRow j) k H v) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  by_cases hk : k = .gammaFive
  · subst k
    exact profile_actual (coupledRow j) (WuPaper.R2Gamma5.original_full_parameters j)
      H hm hH hδ hn m hη he
  · have hp := (coupledRow_geometry j).1
    have hh := Pair.full_profile_actual (coupledRow j) hp k H hm hH m hη hδ he
      (fun ρ hρ => hn (m + 2) (Pair.childEta (coupledRow j) η) ρ (Pair.childEta_pos hp hη) hρ)
    rw [PairLiteral.other_kernel_eq (original_fullH j) k hk H] at hh
    exact hh

end Wu18938Campaign.M1.Confirmed.FullFive
