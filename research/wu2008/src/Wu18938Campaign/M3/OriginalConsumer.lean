import Wu18938Campaign.M3.FullMassOriginal
import Wu18938Campaign.M3.CountConsumer
import WR2Gamma5Original

noncomputable section

namespace Wu18938Campaign.M3

open Finset Real Wu2008DoubleSieve ActualNineFeedback
open Wu2008DoubleSieve.MotherPair WuPaper.R2Gamma5
open scoped Classical

theorem original_four_count_with_defect (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ r : Fin 4,
        secondFunctionalMotherGammaSum (coupledRow r) N δ
            (convolutionWuWindows N Δ V) 5 ≤
          (classicalIntegral (coupledRow r) .gammaFive -
              WuPaper.R2Xi.original66 (wuImprovementLimit true δ) (coupledRow r) + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
            sieveDefect (coupledRow r) N δ (convolutionWuWindows N Δ V) := by
  choose T hT4 hT using (fun r : Fin 4 =>
    actual_count_full_integral_with_defect (original_full_parameters r) k hδ hδhi hε)
  refine ⟨univ.sup T, (hT4 0).trans (le_sup (mem_univ 0)), ?_⟩
  intro N hN i Δ V hb r
  simpa only [fullIntegral_eq_original66 (original_full_parameters r) hδ
    (by linarith : δ < 1 / 2)] using
      hT r N ((le_sup (f := T) (mem_univ r)).trans hN) i Δ V hb

end Wu18938Campaign.M3
