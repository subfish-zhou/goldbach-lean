import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherOriginalWindows
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPayment

/-! # The parameterized actual convolution mother and its common-threshold source port

The positive terms use the accepted prefix dictionary at every arity.
The three negative terms retain their separate original N-windows.
-/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

noncomputable def secondFunctionalMotherGammaSum (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) (j : ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    secondFunctionalMotherGamma N d N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa2)
      (wuLocalCutoff N δ d p.kappa3) (wuLocalCutoff N δ d p.s) j

noncomputable def secondFunctionalMotherRHS (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W p.S + wuBoxPhi N δ W p.kappa1 -
    wuOmega2Sum N δ p.s p.S W - wuOmega2Sum N δ p.kappa2 p.S W -
    wuOmega2Sum N δ p.kappa3 p.S W +
    ∑ j ∈ Icc 5 21, secondFunctionalMotherGammaSum p N δ W j

/-- This identity holds for arbitrary windows, without a source-box premise. -/
theorem secondFunctionalMother_weighted_identity (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      secondFunctionalMotherLocal N d N (wuLocalCutoff N δ d p.S)
        (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa2)
        (wuLocalCutoff N δ d p.kappa3) (wuLocalCutoff N δ d p.s)) =
      secondFunctionalMotherRHS p N δ W := by
  simp only [secondFunctionalMotherLocal, secondFunctionalMotherGamma,
    mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  simp only [secondFunctionalMotherRHS, wuBoxPhi, convolutionSieveCount,
    wuOmega2Sum, wuOmega2, fourthRowMotherSingle, secondFunctionalMotherGammaSum,
    mul_sum, mul_left_comm]
  rw [sum_comm]
  rfl

/-- Finite source inequality with precisely the three actual bad-prime windows. -/
theorem secondFunctionalMother_source_finite
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
      secondFunctionalMotherRHS p N δ (convolutionWuWindows N Δ V) +
        secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) := by
  rw [← secondFunctionalMother_weighted_identity]
  unfold secondFunctionalMotherError wuBoxPhi convolutionSieveCount
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ := secondFunctionalMother_source_cutoffs p hp
    hN hδ hδhi hb hd
  have h := mul_le_mul_of_nonneg_left
    (secondFunctionalMother_original_windows N d hab hbc hce hef)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
  convert h using 1 <;> ring

/-- No mass, error, or all-box conclusion is assumed at this source port. -/
theorem secondFunctionalMother_source
    (k : ℕ) (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          secondFunctionalMotherRHS p N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := secondFunctionalMother_error_relative k p hp hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb
  exact (secondFunctionalMother_source_finite p hp (by omega) hδ hδhi hb).trans
    (add_le_add le_rfl (hT N hN he i Δ V hb))

end Wu2008DoubleSieve
