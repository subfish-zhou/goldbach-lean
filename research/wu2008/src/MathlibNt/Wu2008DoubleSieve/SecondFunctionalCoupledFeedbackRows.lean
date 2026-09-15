import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedback

namespace Wu2008DoubleSieve.SecondFunctionalCoupledFeedback
open SecondFunctionalParameters FourthRowPhiOmega2

theorem row1_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row1.s ≤
          (cost row1 δ - gain row1 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row1 SecondFunctionalCoupled.row1_analytic k hk hδ hδhi hε

theorem row1_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row1.s + (gain row1 δ - cost row1 δ)/5 ≤
      wuImprovementLimit true δ row1.s :=
  actual_limit row1 SecondFunctionalCoupled.row1_analytic hδ hδhi

theorem row2_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row2.s ≤
          (cost row2 δ - gain row2 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row2 SecondFunctionalCoupled.row2_analytic k hk hδ hδhi hε

theorem row2_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row2.s + (gain row2 δ - cost row2 δ)/5 ≤
      wuImprovementLimit true δ row2.s :=
  actual_limit row2 SecondFunctionalCoupled.row2_analytic hδ hδhi

theorem row3_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row3.s ≤
          (cost row3 δ - gain row3 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row3 SecondFunctionalCoupled.row3_analytic k hk hδ hδhi hε

theorem row3_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row3.s + (gain row3 δ - cost row3 δ)/5 ≤
      wuImprovementLimit true δ row3.s :=
  actual_limit row3 SecondFunctionalCoupled.row3_analytic hδ hδhi

theorem row4_mother (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row4.s ≤
          (cost row4 δ - gain row4 δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  mother row4 SecondFunctionalCoupled.row4_analytic k hk hδ hδhi hε

theorem row4_actual_limit {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient row4.s + (gain row4 δ - cost row4 δ)/5 ≤
      wuImprovementLimit true δ row4.s :=
  actual_limit row4 SecondFunctionalCoupled.row4_analytic hδ hδhi

end Wu2008DoubleSieve.SecondFunctionalCoupledFeedback
