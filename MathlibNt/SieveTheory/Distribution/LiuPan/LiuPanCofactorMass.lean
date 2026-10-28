import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

/-!
Independent reciprocal-totient mass API for the cofactor payment in Pan (2.6).
This is a COARSE TWO-LOG bound, not the printed one-log estimate. It reuses
production's finite divisor/harmonic proof, with no new Mertens analysis.
-/
namespace AnalyticNumberTheory.LargeSieve.PanCofactor
open Finset
open scoped BigOperators

/-- Existing finite divisor estimate, made uniform in the ambient cutoff.
Both D=0 and D=1 are included; no logarithm monotonicity at zero is needed. -/
theorem reciprocal_totient_mass_le_log_sq {D N : ℕ} (hDN : D ≤ N) :
    (∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
  have hH : conductorHarmonicFactor D ≤ 1 + Real.log (N : ℝ) :=
    (conductorHarmonicFactor_mono hDN).trans (conductorHarmonicFactor_le N)
  exact (sum_inv_totient_le_harmonic_sq D).trans
    ((sq_le_sq₀ (conductorHarmonicFactor_nonneg D)
      ((conductorHarmonicFactor_nonneg D).trans hH)).mpr hH)


end AnalyticNumberTheory.LargeSieve.PanCofactor