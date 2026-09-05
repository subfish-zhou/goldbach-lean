import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4RawSiegel
import MathlibNt.AnalyticNumberTheory.LargeSieve.LandauSiegelToStandardBVCanonicalSmoothing
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6AllLevelSmall

noncomputable section
namespace AnalyticNumberTheory.LargeSieve

/-- The existing low source with its raw Siegel input now proved internally. -/
theorem fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource :
    NonprincipalPrimitivePsiSiegelWalfiszSource :=
  nonprincipalPrimitivePsiSiegelWalfiszSource_of_rawLandauSiegelLowerBound
    fourFactor_rawLandauSiegelLowerBound
    standardBVCanonicalSmoothing_contDiff standardBVCanonicalSmoothing_nonneg
    standardBVCanonicalSmoothing_support standardBVCanonicalSmoothing_mass_one

/-- Unconditional Standard BV through the preserved nonprincipal-primitive endpoint. -/
theorem fourFactor_standardBombieriVinogradov :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource

/-- All actual cells under the existing rounded parameters and conductor cutoff.
The corrected positive-level kernel and finite-height level-zero repair are retained.
This is not the final Chen prime theorem or a literal full-height contour claim. -/
theorem chen1973Lemma6_all_level_actual_cell_small_unconditional
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B lastD level k m : ℕ,
      0 < L → 0 < B →
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) → Real.log x ^ (100 : ℕ) < L+1 →
      (B : ℝ) ≤ (x : ℝ)^((13:ℝ)/30) → (x : ℝ)^((13:ℝ)/30) < B+1 →
      L * 2^level ≤ 2*lastD → (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6NmBlockActual x L level B k m ≤ C*x/Real.log x^20 := by
  exact chen1973Lemma6_all_level_actual_cell_small_of_rawLandauSiegel
    fourFactor_rawLandauSiegelLowerBound ε hε hεu

end AnalyticNumberTheory.LargeSieve
