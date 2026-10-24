import WR2XiNineCorrected

/-! A rational arithmetic candidate for the exact corrected system.
The entrywise integral lower bounds for this table are NOT proved here.
The actual-H consumer keeps those missing bounds as explicit hypotheses.
-/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open ActualNineFeedback NodeExtension NineFeedbackStrength
open scoped BigOperators

/-- Candidate lower matrix; its analytic comparison remains to be certified. -/
def lowerMatrix : Fin 9 → Fin 9 → ℝ := ![
  ![77/500, 13/500, 13/500, 13/500, 27/1000, 27/1000, 27/1000, 7/250, 7/250],
  ![19/125, 1/40, 13/500, 13/500, 13/500, 27/1000, 27/1000, 27/1000, 27/1000],
  ![151/1000, 1/40, 1/40, 1/40, 13/500, 13/500, 13/500, 27/1000, 27/1000],
  ![77/500, 23/1000, 3/125, 1/40, 1/40, 13/500, 13/500, 13/500, 27/1000],
  ![159/1000, 23/1000, 3/125, 1/40, 1/40, 13/500, 13/500, 13/500, 27/1000],
  ![4/25, 23/1000, 3/125, 3/125, 1/40, 1/40, 13/500, 13/500, 13/500],
  ![41/250, 23/1000, 3/125, 3/125, 1/40, 1/40, 13/500, 13/500, 13/500],
  ![173/1000, 23/1000, 3/125, 3/125, 1/40, 1/40, 13/500, 13/500, 13/500],
  ![191/1000, 3/125, 1/40, 1/40, 13/500, 13/500, 27/1000, 27/1000, 27/1000]]

/-- Rational subsolution of lowerMatrix, not yet an unconditional bound for actual H. -/
def lowerH : Fin 9 → ℝ := ![11133/500000, 21591/1000000, 20159/1000000, 563/31250, 3939/250000, 6447/500000, 9961/1000000, 3841/500000, 7139/1000000]

theorem lowerH_nonneg (i : Fin 9) : 0 ≤ lowerH i := by
  fin_cases i <;> norm_num [lowerH]

theorem arithmetic_subsolution (i : Fin 9) :
    lowerH i ≤ publication i + matrixApply lowerMatrix lowerH i := by
  have hpub : publication i =
      (![15826357/1000000000, 15247971/1000000000, 13898757/1000000000,
        11776059/1000000000, 9405211/1000000000, 6558950/1000000000,
        3536751/1000000000, 1056651/1000000000, 0] : Fin 9 → ℝ) i := by
    fin_cases i <;> rfl
  rw [hpub]
  fin_cases i <;> norm_num [lowerH, lowerMatrix, matrixApply, Fin.sum_univ_succ]

/-- Conditional consumer: all 81 analytic entry bounds are still required. -/
theorem actual_lower_of_entry_bounds
    (hentry : ∀ i k, lowerMatrix i k ≤ correctedNineMatrix i k) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ i, lowerH i ≤ actualNine δ i := by
  obtain ⟨d, hd, hcap, hcompare⟩ := corrected_nine_comparison
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr
  apply hcompare δ hδ hr lowerH
  intro i
  apply (arithmetic_subsolution i).trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hentry i k) (lowerH_nonneg k)

end WuPaper.R2Xi.RationalCandidate
