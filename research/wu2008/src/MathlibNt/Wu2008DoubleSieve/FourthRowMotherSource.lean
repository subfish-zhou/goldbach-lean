import MathlibNt.Wu2008DoubleSieve.FourthRowMotherOriginalWindows
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherGamma16
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPayment

/-! # The actual fourth-row fivefold prefix mother at one common source threshold

The negative terms retain their original N-windows. All five surviving
triple addends remain separate, and the last addend is the accepted
Gamma16 prefix sum, not its raw or quotient analogue.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowMotherGamma5 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    fourthRowMotherPair N d N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (291 / 100)) (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (291 / 100))

noncomputable def fourthRowMotherGamma6 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    fourthRowMotherPair N d N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))
      (wuLocalCutoff N δ d (5 / 2))

noncomputable def fourthRowMotherPrefixSum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (cs : List ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    fourthRowMotherPrefixTerm N d N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))
      (wuLocalCutoff N δ d (5 / 2)) cs

noncomputable def fourthRowMotherRHS {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * wuBoxPhi N δ W (103 / 25) + wuBoxPhi N δ W (89 / 25) -
    2 * wuOmega2Sum N δ (5 / 2) (103 / 25) W -
    wuOmega2Sum N δ (291 / 100) (103 / 25) W +
    fourthRowMotherGamma5 N δ W + fourthRowMotherGamma6 N δ W +
    fourthRowMotherPrefixSum N δ W [0, 0] +
    fourthRowMotherPrefixSum N δ W [0, 1] +
    wuOmega3Sum N δ (5 / 2) (89 / 25) W +
    fourthRowMotherPrefixSum N δ W [1, 1, 2] +
    fourthRowMotherPrefixSum N δ W [1, 2, 2] +
    fourthRowMotherPrefixSum N δ W [0, 1, 2] +
    fourthRowMotherPrefixSum N δ W [0, 2, 2] +
    gamma16PrefixSum N δ W

theorem fourthRowMother_weighted_identity {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        fourthRowMotherLocal N d N (wuLocalCutoff N δ d (103 / 25))
          (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))
          (wuLocalCutoff N δ d (5 / 2))) =
      fourthRowMotherRHS N δ (convolutionWuWindows N Δ V) := by
  have h16 :
      (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          fourthRowMotherPrefixTerm N d N (wuLocalCutoff N δ d (103 / 25))
            (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))
            (wuLocalCutoff N δ d (5 / 2)) [2, 2, 2, 2]) =
        gamma16PrefixSum N δ (convolutionWuWindows N Δ V) := by
    unfold gamma16PrefixSum
    apply sum_congr rfl
    intro d hd
    obtain ⟨_, _, hab, hbc, _⟩ := fourthRowMother_source_cutoffs
      (by omega : 2 ≤ N) hδ hδhi hb hd
    rw [fourthRowMother_gamma16_mass hN he (hab.trans hbc) hbc]
  simp only [fourthRowMotherLocal, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [h16]
  simp only [fourthRowMotherRHS, wuBoxPhi, convolutionSieveCount, wuOmega2Sum,
    wuOmega2, wuOmega3Sum, wuOmega3, fourthRowMotherGamma5, fourthRowMotherGamma6,
    fourthRowMotherPrefixSum, fourthRowMotherSingle, fourthRowMotherNine, mul_sum,
    mul_assoc, mul_left_comm]
  rfl

theorem fourthRowMother_source_finite {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
      fourthRowMotherRHS N δ (convolutionWuWindows N Δ V) +
        fourthRowMotherError N δ (convolutionWuWindows N Δ V) := by
  rw [← fourthRowMother_weighted_identity hN he hδ hδhi hb]
  unfold fourthRowMotherError wuBoxPhi convolutionSieveCount
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  obtain ⟨_, _, hab, hbc, hcf⟩ := fourthRowMother_source_cutoffs
    (by omega : 2 ≤ N) hδ hδhi hb hd
  have h := mul_le_mul_of_nonneg_left (fourthRowMother_original_windows N d hab hbc hcf)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
  convert h using 1 <;> ring

theorem fourthRowMother_source (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5 / 2) ≤
          fourthRowMotherRHS N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := fourthRowMother_error_relative k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb
  exact (fourthRowMother_source_finite (hT4.trans hN) he hδ hδhi hb).trans
    (add_le_add le_rfl (hT N hN he i Δ V hb))

end Wu2008DoubleSieve
