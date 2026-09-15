import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleOrderedSource

namespace Wu2008DoubleSieve
open Finset
open scoped Classical

/-- Actual Gamma10: M=N, with sigma applied once per outer d.
The actual source box supplies every cutoff comparison. -/
theorem secondFunctionalMother_gamma10_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 10 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s))).filter (fun t =>
              (wuLocalCutoff N δ d p.kappa1) ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (wuLocalCutoff N δ d p.kappa2) ∧
              (wuLocalCutoff N δ d p.kappa1) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < (wuLocalCutoff N δ d p.kappa2) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < (wuLocalCutoff N δ d p.s)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma10_ordered_source N d N hab hbc hce hef]

/-- Actual Gamma11: M=N, with sigma applied once per outer d.
The actual source box supplies every cutoff comparison. -/
theorem secondFunctionalMother_gamma11_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 11 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s))).filter (fun t =>
              (wuLocalCutoff N δ d p.kappa1) ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (wuLocalCutoff N δ d p.kappa2) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < (wuLocalCutoff N δ d p.kappa3) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < (wuLocalCutoff N δ d p.kappa3)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma11_ordered_source N d N hab hbc hce hef]

/-- Actual Gamma12: M=N, with sigma applied once per outer d.
The actual source box supplies every cutoff comparison. -/
theorem secondFunctionalMother_gamma12_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 12 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s))).filter (fun t =>
              (wuLocalCutoff N δ d p.S) ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (wuLocalCutoff N δ d p.kappa1) ∧
              (wuLocalCutoff N δ d p.S) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < (wuLocalCutoff N δ d p.kappa1) ∧
              (wuLocalCutoff N δ d p.kappa3) ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < (wuLocalCutoff N δ d p.s)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma12_ordered_source N d N hab hbc hce hef]

/-- Actual Gamma13: M=N, with sigma applied once per outer d.
The actual source box supplies every cutoff comparison. -/
theorem secondFunctionalMother_gamma13_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 13 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s))).filter (fun t =>
              (wuLocalCutoff N δ d p.S) ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (wuLocalCutoff N δ d p.kappa1) ∧
              (wuLocalCutoff N δ d p.kappa1) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < (wuLocalCutoff N δ d p.kappa2) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < (wuLocalCutoff N δ d p.s)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma13_ordered_source N d N hab hbc hce hef]

/-- Actual Gamma14: M=N, with sigma applied once per outer d.
The actual source box supplies every cutoff comparison. -/
theorem secondFunctionalMother_gamma14_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 14 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s))).filter (fun t =>
              (wuLocalCutoff N δ d p.S) ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (wuLocalCutoff N δ d p.kappa1) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < (wuLocalCutoff N δ d p.s) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < (wuLocalCutoff N δ d p.s)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma14_ordered_source N d N hab hbc hce hef]

/-- Actual Gamma15: M=N, with sigma applied once per outer d.
The actual source box supplies every cutoff comparison. -/
theorem secondFunctionalMother_gamma15_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 15 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s))).filter (fun t =>
              (wuLocalCutoff N δ d p.kappa1) ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < (wuLocalCutoff N δ d p.kappa2) ∧
              (wuLocalCutoff N δ d p.kappa2) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < (wuLocalCutoff N δ d p.kappa3) ∧
              (wuLocalCutoff N δ d p.kappa3) ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < (wuLocalCutoff N δ d p.s)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma15_ordered_source N d N hab hbc hce hef]

end Wu2008DoubleSieve
