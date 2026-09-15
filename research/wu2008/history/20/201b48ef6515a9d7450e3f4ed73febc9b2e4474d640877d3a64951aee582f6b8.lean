import WR2Gamma5CountTransport
import WRMapMMatrixGeometry

noncomputable section

namespace WuPaper.R2Gamma5

open Finset Set Real Wu2008DoubleSieve Wu2008DoubleSieve.MotherPair
open ActualNineFeedback
open scoped Classical

theorem original_full_parameters (r : Fin 4) : FullParameters (coupledRow r) := by
  have hg := WuPaper.RMapMMatrix.original_four_rows_qualified r
  have hl : 1 ≤ (coupledRow r).S - 2 * (coupledRow r).S / (coupledRow r).kappa2 :=
    (hg.2.2.2.2.2.2.2.2.2.1 5).1
  refine ⟨?_, hl⟩
  fin_cases r
  · exact row1_fullH.toAnalyticParameters
  · exact row2_fullH.toAnalyticParameters
  · exact row3_fullH.toAnalyticParameters
  · exact row4_fullH.toAnalyticParameters

theorem original_fullHMass_uniform (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ (r : Fin 4) (A B C D : ℝ), FullRectangle (coupledRow r) A B C D →
        (wuImprovementLimit true δ ((coupledRow r).S * (1 - A - C)) *
            rectIntegral A B C D - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          fullHMass (coupledRow r) N δ (convolutionWuWindows N Δ V)
            (rectLabels N δ (convolutionWuWindows N Δ V) A B C D) := by
  choose T _ hT using fun r : Fin 4 =>
    fullHMass_rectangle_producer (coupledRow r) (original_full_parameters r)
      k hδ hδhi hε
  refine ⟨max 4 (univ.sup T), le_max_left _ _, ?_⟩
  intro N hN i Δ V hb r A B C D hr
  have hrN : T r ≤ N :=
    (le_sup (f := T) (mem_univ r)).trans ((le_max_right _ _).trans hN)
  exact hT r N hrN i Δ V hb A B C D hr

theorem original_full_count_identity (r : Fin 4)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum (coupledRow r) N δ
        (convolutionWuWindows N Δ V) 5 =
      ∑ x ∈ termLabels (coupledRow r) .gammaFive N δ (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          (sourceSieveCount N (gamma5ClassicalProduct x) (gamma5ClassicalProduct x * N)
            (wuLocalCutoff N δ (gamma5ClassicalProduct x)
              (localRatio (coupledRow r) N δ x)) : ℝ) :=
  full_count_exact_phi_atoms (original_full_parameters r) hN hδ hδhi hb

theorem unit_pair_no_permutation {N k : ℕ} {δ Δ t u : ℝ}
    (hR : 1 < (N : ℝ) ^ (1 / 2 - δ)) (htu : t < u)
    (hbad : 1 < u + 2 * t) (e : Equiv.Perm (Fin 2)) :
    ¬ wuSourceBox k δ N 2 Δ
      ((![((N : ℝ) ^ (1 / 2 - δ)) ^ u,
          ((N : ℝ) ^ (1 / 2 - δ)) ^ t] : Fin 2 → ℝ) ∘ e) := by
  intro hb
  by_cases he0 : e 0 = 0
  · have he1 : e 1 = 1 := by
      have hn : e 1 ≠ 0 := by
        intro h
        have heq : e 1 = e 0 := h.trans he0.symm
        have hne : (1 : Fin 2) ≠ 0 := by decide
        exact hne (e.injective heq)
      rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h | h
      · exact False.elim (hn h)
      · exact h
    have heid : ∀ j : Fin 2, e j = j := by
      intro j
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact he0
      · exact he1
    apply unit_pair_not_sourceBox hR hbad
    simpa only [Function.comp_def, heid] using hb
  · have he0' : e 0 = 1 := by
      rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h | h
      · exact False.elim (he0 h)
      · exact h
    have he1 : e 1 = 0 := by
      have hn : e 1 ≠ 1 := by
        intro h
        have heq : e 1 = e 0 := h.trans he0'.symm
        have hne : (1 : Fin 2) ≠ 0 := by decide
        exact hne (e.injective heq)
      rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h | h
      · exact h
      · exact False.elim (hn h)
    have ha := hb.2.2.2.1 (show (0 : Fin 2) ≤ 1 by decide)
    simp only [Function.comp_apply, he0', he1, Matrix.cons_val_zero,
      Matrix.cons_val_one] at ha
    have hlt := rpow_lt_rpow_of_exponent_lt hR htu
    exact (not_lt_of_ge ha) hlt

#check @WuPaper.R2Gamma5.original_full_parameters
#print axioms WuPaper.R2Gamma5.original_full_parameters
#check @WuPaper.R2Gamma5.original_fullHMass_uniform
#print axioms WuPaper.R2Gamma5.original_fullHMass_uniform
#check @WuPaper.R2Gamma5.original_full_count_identity
#print axioms WuPaper.R2Gamma5.original_full_count_identity
#check @WuPaper.R2Gamma5.unit_pair_no_permutation
#print axioms WuPaper.R2Gamma5.unit_pair_no_permutation

end WuPaper.R2Gamma5
