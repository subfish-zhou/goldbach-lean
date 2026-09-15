import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledMother

namespace Wu2008DoubleSieve.SecondFunctionalCoupled
open SecondFunctionalParameters FourthRowPhiOmega2

theorem row1_analytic : MotherPair.AnalyticParameters row1 := by
  refine ⟨row1_motherAdmissible, ?_, ?_, ?_, ?_⟩ <;> norm_num [row1]

/-- The complete finite-source conclusion for the original row, including degenerate bands. -/
theorem row1_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row1.s ≤
          (coefficient row1 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row1 row1_analytic k hk hδ hδhi hε

/-- Actual final-depth H feedback, not a numerical closure claim. -/
theorem row1_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row1.s -
      (4 * wuUpperCoefficient row1.S + wuUpperCoefficient row1.kappa1 -
        4 * wuImprovementLimit true δ row1.S - wuImprovementLimit true δ row1.kappa1 -
        J δ row1.s row1.S - J δ row1.kappa2 row1.S - J δ row1.kappa3 row1.S +
        (2/(1-2*δ))*omega3XIntegralEnvelope row1.kappa3 row1.kappa1 +
        MotherPair.fourIntegralUpper row1 δ + (2/(1-2*δ))*jointSup row1)/5 ≤
      wuImprovementLimit true δ row1.s :=
  actual_limit row1 row1_analytic hδ hδhi

theorem row2_analytic : MotherPair.AnalyticParameters row2 := by
  refine ⟨row2_motherAdmissible, ?_, ?_, ?_, ?_⟩ <;> norm_num [row2]

/-- The complete finite-source conclusion for the original row, including degenerate bands. -/
theorem row2_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row2.s ≤
          (coefficient row2 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row2 row2_analytic k hk hδ hδhi hε

/-- Actual final-depth H feedback, not a numerical closure claim. -/
theorem row2_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row2.s -
      (4 * wuUpperCoefficient row2.S + wuUpperCoefficient row2.kappa1 -
        4 * wuImprovementLimit true δ row2.S - wuImprovementLimit true δ row2.kappa1 -
        J δ row2.s row2.S - J δ row2.kappa2 row2.S - J δ row2.kappa3 row2.S +
        (2/(1-2*δ))*omega3XIntegralEnvelope row2.kappa3 row2.kappa1 +
        MotherPair.fourIntegralUpper row2 δ + (2/(1-2*δ))*jointSup row2)/5 ≤
      wuImprovementLimit true δ row2.s :=
  actual_limit row2 row2_analytic hδ hδhi

theorem row3_analytic : MotherPair.AnalyticParameters row3 := by
  refine ⟨row3_motherAdmissible, ?_, ?_, ?_, ?_⟩ <;> norm_num [row3]

/-- The complete finite-source conclusion for the original row, including degenerate bands. -/
theorem row3_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row3.s ≤
          (coefficient row3 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row3 row3_analytic k hk hδ hδhi hε

/-- Actual final-depth H feedback, not a numerical closure claim. -/
theorem row3_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row3.s -
      (4 * wuUpperCoefficient row3.S + wuUpperCoefficient row3.kappa1 -
        4 * wuImprovementLimit true δ row3.S - wuImprovementLimit true δ row3.kappa1 -
        J δ row3.s row3.S - J δ row3.kappa2 row3.S - J δ row3.kappa3 row3.S +
        (2/(1-2*δ))*omega3XIntegralEnvelope row3.kappa3 row3.kappa1 +
        MotherPair.fourIntegralUpper row3 δ + (2/(1-2*δ))*jointSup row3)/5 ≤
      wuImprovementLimit true δ row3.s :=
  actual_limit row3 row3_analytic hδ hδhi

theorem row4_analytic : MotherPair.AnalyticParameters row4 := by
  refine ⟨row4_motherAdmissible, ?_, ?_, ?_, ?_⟩ <;> norm_num [row4]

/-- The complete finite-source conclusion for the original row, including degenerate bands. -/
theorem row4_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row4.s ≤
          (coefficient row4 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row4 row4_analytic k hk hδ hδhi hε

/-- Actual final-depth H feedback, not a numerical closure claim. -/
theorem row4_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row4.s -
      (4 * wuUpperCoefficient row4.S + wuUpperCoefficient row4.kappa1 -
        4 * wuImprovementLimit true δ row4.S - wuImprovementLimit true δ row4.kappa1 -
        J δ row4.s row4.S - J δ row4.kappa2 row4.S - J δ row4.kappa3 row4.S +
        (2/(1-2*δ))*omega3XIntegralEnvelope row4.kappa3 row4.kappa1 +
        MotherPair.fourIntegralUpper row4 δ + (2/(1-2*δ))*jointSup row4)/5 ≤
      wuImprovementLimit true δ row4.s :=
  actual_limit row4 row4_analytic hδ hδhi

end Wu2008DoubleSieve.SecondFunctionalCoupled
