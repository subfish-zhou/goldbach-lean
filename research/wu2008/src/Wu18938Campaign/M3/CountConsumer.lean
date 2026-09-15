import Wu18938Campaign.M3.FullMassApprox
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalPorts

noncomputable section

namespace Wu18938Campaign.M3

open Finset Real Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair WuPaper.R2Gamma5
open scoped Classical

def sieveDefect {i : ℕ} (p : SecondFunctionalParameters) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  secondFunctionalMotherGammaSum p N δ W 5 +
    fullHMass p N δ W (termLabels p .gammaFive N δ W) -
    gamma5ClassicalMainMass N δ W (termLabels p .gammaFive N δ W)

theorem actual_count_full_integral_with_defect {p : SecondFunctionalParameters}
    (hp : FullParameters p) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 ≤
          (classicalIntegral p .gammaFive - fullIntegral p δ + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
            sieveDefect p N δ (convolutionWuWindows N Δ V) := by
  obtain ⟨TH, hTH4, hH⟩ := fullHMass_integral_lower hp k hδ hδhi (half_pos hε)
  obtain ⟨TM, _, hM⟩ := term_mass p hp.toAnalyticParameters k hδ hδhi (half_pos hε)
  refine ⟨max TH TM, hTH4.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb
  have hmass := hM N ((le_max_right _ _).trans hN) i Δ V hb .gammaFive
  have hgain := hH N ((le_max_left _ _).trans hN) i Δ V hb
  have hupper := (abs_le.mp hmass).2
  unfold sieveDefect
  linarith only [hupper, hgain]

end Wu18938Campaign.M3
