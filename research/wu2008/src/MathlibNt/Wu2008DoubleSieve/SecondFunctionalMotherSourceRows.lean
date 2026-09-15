import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSource

/-! # The four actual row-record instances of the generic source theorem -/
namespace Wu2008DoubleSieve
open SecondFunctionalParameters

theorem secondFunctionalMother_row1_source (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row1.s ≤
          secondFunctionalMotherRHS row1 N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  secondFunctionalMother_source k row1 row1_motherAdmissible hδ hδhi hε

theorem secondFunctionalMother_row2_source (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row2.s ≤
          secondFunctionalMotherRHS row2 N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  secondFunctionalMother_source k row2 row2_motherAdmissible hδ hδhi hε

theorem secondFunctionalMother_row3_source (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row3.s ≤
          secondFunctionalMotherRHS row3 N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  secondFunctionalMother_source k row3 row3_motherAdmissible hδ hδhi hε

theorem secondFunctionalMother_row4_source (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) row4.s ≤
          secondFunctionalMotherRHS row4 N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  secondFunctionalMother_source k row4 row4_motherAdmissible hδ hδhi hε

end Wu2008DoubleSieve
