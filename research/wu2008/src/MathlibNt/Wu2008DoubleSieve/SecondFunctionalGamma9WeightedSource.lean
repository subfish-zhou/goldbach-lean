import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9OrderedSource

namespace Wu2008DoubleSieve
open Finset
open scoped Classical

/-- Actual convolution sigma is applied once per d, with the original M=N window.
The source-box geometry supplies every cutoff comparison internally; no equality
between kappa3 and s, coprimality with d, or source identity is assumed. -/
theorem secondFunctionalMother_gamma9_weighted_ordered_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 9 =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ t ∈ orderedTriples (primeWindow N
            (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa3)),
            (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  unfold secondFunctionalMotherGammaSum
  apply sum_congr rfl
  intro d hd
  obtain ⟨_, _, hab, hbc, hce, hef⟩ :=
    secondFunctionalMother_source_cutoffs p hp hN hδ hδhi hb hd
  rw [secondFunctionalMother_gamma9_ordered_source N d N hab hbc hce hef]

end Wu2008DoubleSieve
