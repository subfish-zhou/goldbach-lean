import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorLocalPrimitiveLargeSieve
import MathlibNt.AnalyticNumberTheory.Vaughan.HighConductorVaughanTypeIIFixedShell
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVHighConductorLocalAssembly

/-!
# Conductor-local input on the actual Vaughan rows

This module specializes the arbitrary-coefficient conductor-local square input
at the two row types which occur in the production Type-I and Type-II shell
ledgers.  It deliberately stops before shell aggregation: the production
Type-II fixed-shell family has not yet been identified with the canonical
hyperbolic shells in the actual Vaughan decomposition.
-/

namespace AnalyticNumberTheory.LargeSieve

open Filter
open scoped Topology

noncomputable section

/-- The single allowed high analytic input, with its harmless positive
constant existentially packaged. -/
def ConductorLocalPrimitiveLargeSieveSource : Prop :=
  ∃ K : ℝ, 0 < K ∧ ConductorLocalPrimitiveLargeSieve K

/-- The arbitrary-row conductor-local estimate specializes directly to every
literal Vaughan Type-I row.  No Type-I mean estimate is assumed. -/
theorem highConductorVaughanTypeIRow_mean_le_of_conductorLocal
    {K : ℝ} (hK : 0 ≤ K) (hLS : ConductorLocalPrimitiveLargeSieve K)
    (R Q L X : ℕ) (a : ℂ) (b : ℤ → ℂ) (M : ℤ)
    (hR : 0 < R) (hQ : 0 < Q)
    (hdiag : (L : ℝ) *
      conductorLocalRowEnergy (vaughanTypeIRowCoefficient a b) M L ≤ (X : ℝ) ^ 2)
    (henergy : conductorLocalRowEnergy
      (vaughanTypeIRowCoefficient a b) M L ≤ (X : ℝ)) :
    highConductorPrimitiveMean R Q
        (highConductorVaughanTypeIRowAmplitude a b M L) ≤
      K * ((Nat.log2 L + 1 : ℕ) : ℝ) *
        ((X : ℝ) / Real.sqrt R + (Q : ℝ) * Real.sqrt X) := by
  change highConductorPrimitiveMean R Q (fun d χ =>
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIRowCoefficient a b) M L d χ)) ≤ _
  exact highConductorPrimitiveRowMean_le_of_conductorLocal hK hLS
    R Q L X (vaughanTypeIRowCoefficient a b) M hR hQ hdiag henergy

/-- The same analytic input specializes to every physical Type-II collected
row, retaining the actual shell length `N / 2^k` and product cutoff.  No
fixed-shell or final high-mean estimate is assumed. -/
theorem highConductorVaughanTypeIICollectedRow_mean_le_of_conductorLocal
    {K : ℝ} (hK : 0 ≤ K) (hLS : ConductorLocalPrimitiveLargeSieve K)
    (R Q N k X r : ℕ) (c : ℕ → ℕ → ℂ)
    (hR : 0 < R) (hQ : 0 < Q)
    (hdiag : (vaughanTypeIIFixedShellLength N k : ℝ) *
      conductorLocalRowEnergy (vaughanTypeIICollectedRowCoefficient N r c) 0
        (vaughanTypeIIFixedShellLength N k) ≤ (X : ℝ) ^ 2)
    (henergy : conductorLocalRowEnergy
      (vaughanTypeIICollectedRowCoefficient N r c) 0
        (vaughanTypeIIFixedShellLength N k) ≤ (X : ℝ)) :
    highConductorPrimitiveMean R Q (fun d χ =>
        Real.sqrt (primitiveCharacterPrefixMaxSquare
          (vaughanTypeIICollectedRowCoefficient N r c) 0
          (vaughanTypeIIFixedShellLength N k) d χ)) ≤
      K * ((Nat.log2 (vaughanTypeIIFixedShellLength N k) + 1 : ℕ) : ℝ) *
        ((X : ℝ) / Real.sqrt R + (Q : ℝ) * Real.sqrt X) := by
  exact highConductorPrimitiveRowMean_le_of_conductorLocal hK hLS
    R Q (vaughanTypeIIFixedShellLength N k) X
      (vaughanTypeIICollectedRowCoefficient N r c) 0 hR hQ hdiag henergy

/-- The packaged square-level source always carries the already-proved scalar
Pan payment.  This is the complete source-independent terminal scalar step. -/
theorem ConductorLocalPrimitiveLargeSieveSource.panPayable
    (hLS : ConductorLocalPrimitiveLargeSieveSource) (A κ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ConductorLocalPrimitiveLargeSieve K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let C := conductorLocalPanConductorExponent A κ
        let B := conductorLocalPanModulusExponent A κ
        let R := logConductorThreshold N C
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        Real.log (N : ℝ) ^ κ *
            ((N : ℝ) / Real.sqrt R + (Q : ℝ) * Real.sqrt N) ≤
          2 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨K, hK, hlocal⟩ := hLS
  exact ⟨K, hK, hlocal, conductorLocal_high_scales_pan_payable A κ⟩

end
end AnalyticNumberTheory.LargeSieve
