import FeedbackSystem

/-!
Wu04 Lemma 5.2: recover the exact classical logarithmic part on the
current actual mother. The cost below is NOT identified with the printed
sum I_{2,9}+...+I_{2,21}: it retains the actual legal kernels and unit terms.
No published decimal and no delta-zero sieve function is assumed.
-/
namespace Wu08OriginalPsiRecovery
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open SecondFunctionalSignedCore

noncomputable section

def classicalNumerator (p : SecondFunctionalParameters) : ℝ :=
  fourthRowClassicalJ p.s p.S + fourthRowClassicalJ p.kappa3 p.kappa1 -
    2 * fourthRowClassicalL p.S - 2 * fourthRowClassicalL p.kappa1 -
    fourthRowClassicalL p.kappa2

/-- Exact Wu04 logarithmic numerator, with all four actual Gamma rectangles
joined by the previously proved integral identities. -/
theorem coupledBase_eq_original_logs {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) :
    coupledBase p = (classicalNumerator p - 2 * coupledCostMass p) / 5 := by
  have hm := hp.1.mother
  have hs3 := hm.s_le_kappa3
  have h32 := hm.kappa3_lt_kappa2.le
  have h21 := hm.kappa2_lt_kappa1.le
  have h1S := hm.kappa1_le_S
  have hclassic := SecondFunctionalClassicalAlgebra.coefficient_eq hp.1.two_lt_s.le
    hp.1.s_le_three hp.2.1 h1S hp.1.S_le_five
    (hp.1.two_lt_s.trans_le (hs3.trans h32)) (h21.trans h1S)
    (hp.1.two_lt_s.trans_le hs3) (h32.trans h21)
  rw [coupledBase, classical_eq_triangles hp.1]
  unfold classicalNumerator
  linarith only [hclassic]

/-- Source producer for every admissible coupled parameter set at genuine
positive delta. The entire cost, not merely an elementary cap, is retained. -/
theorem original_logs_actual_lower {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    classicalNumerator p / 5 -
        2 * coupledCostMass p / (5 * (1 - 2 * δ)) +
      coupledFeedback p (actualNine δ) ≤ wuImprovementLimit true δ p.s := by
  have h := coupled_actual hp hd hh
  rw [coupledBase_eq_original_logs hp] at h
  have he : (classicalNumerator p - 2 * coupledCostMass p) / 5 -
      deltaLoss δ * coupledLoss p = classicalNumerator p / 5 -
        2 * coupledCostMass p / (5 * (1 - 2 * δ)) := by
    unfold deltaLoss coupledLoss
    field_simp [show 1 - 2 * δ ≠ 0 by linarith]
    ring
  rwa [he] at h

/-- The four published parameter choices all consume the same actual source;
this is not an assumption of the four published Psi2 decimals. -/
theorem four_original_rows {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 4) :
    classicalNumerator (coupledRow i) / 5 -
        2 * coupledCostMass (coupledRow i) / (5 * (1 - 2 * δ)) +
      coupledFeedback (coupledRow i) (actualNine δ) ≤
        wuImprovementLimit true δ (upperNode ⟨i.val, by omega⟩) := by
  have h := original_logs_actual_lower (coupledRow_geometry i) hd hh
  rwa [coupledRow_node] at h

/-- Strong-input admission is pointwise on the original unbounded phi domain.
All suprema are eliminated here by their actual definitions, not numerical
maximization or an unsupported identification with Wu04's printed costs. -/
theorem original_cost_of_pointwise {p : SecondFunctionalParameters}
    {I K : ℝ}
    (hI : ∀ φ : ℝ, 2 ≤ φ → omega3XIntegral p.kappa3 p.kappa1 φ ≤ I)
    (hK : ∀ φ : ℝ, 2 ≤ φ → SecondFunctionalCoupled.kernel p φ ≤ K) :
    coupledCostMass p ≤ I + K := by
  have hi : omega3XIntegralEnvelope p.kappa3 p.kappa1 ≤ I := by
    apply csSup_le
    · exact ⟨omega3XIntegral p.kappa3 p.kappa1 2, 2,
        (by simp : (2 : ℝ) ∈ Set.Ici 2), rfl⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      exact hI φ hφ
  have hk : SecondFunctionalCoupled.jointSup p ≤ K := by
    apply csSup_le (SecondFunctionalCoupled.values_nonempty p)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hK φ hφ
  exact add_le_add hi hk

/-- A source-compatible quantitative producer. To use published constants one
must PROVE the two pointwise majorants; no record stores a desired conclusion.
The logarithmic part, all feedback, and fixed-positive-delta debit remain. -/
theorem quantitative_source_producer {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) {I K δ : ℝ}
    (hI : ∀ φ : ℝ, 2 ≤ φ → omega3XIntegral p.kappa3 p.kappa1 φ ≤ I)
    (hK : ∀ φ : ℝ, 2 ≤ φ → SecondFunctionalCoupled.kernel p φ ≤ K)
    (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    classicalNumerator p / 5 - 2 * (I + K) / (5 * (1 - 2 * δ)) +
      coupledFeedback p (actualNine δ) ≤ wuImprovementLimit true δ p.s := by
  have hcost := original_cost_of_pointwise hI hK
  have hden : 0 ≤ 5 * (1 - 2 * δ) := by linarith
  have hcost' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2)) hden
  have hsrc := original_logs_actual_lower hp hd hh
  linarith only [hcost', hsrc]

end
end Wu08OriginalPsiRecovery
