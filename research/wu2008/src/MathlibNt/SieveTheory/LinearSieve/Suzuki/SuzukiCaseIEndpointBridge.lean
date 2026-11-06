import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseII
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseIEventually
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection14LegalDomainBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- A natural ceiling is exactly the natural cutoff representing the strict real
inequality `p < y`. -/
theorem suzukiSupportedBelow_ceil_real
    (S : BoundingSieve) (y : ℝ) :
    suzukiSupportedBelow S ⌈y⌉₊ =
      S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < y) := by
  ext p
  simp [suzukiSupportedBelow, Nat.lt_ceil]

/-- At the κ=1 source endpoint `β = 2`, the real power coordinate has exactly
cube `D`. -/
theorem caseI_endpoint_power_cube
    {β D y : ℝ} (hD : 0 ≤ D) (hβ : β = 2)
    (hy : y = D ^ (1 / (β + 1))) :
    y ^ 3 = D := by
  subst β
  rw [hy]
  norm_num
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hD]
  norm_num

/-- The exact boundary condition needed for the natural recurrence.  Unlike the
coarser `ynat^3 ≤ Dnat`, this condition is preserved by choosing
`ynat = ceil y`: every integer `p < ceil y` satisfies `p < y`. -/
theorem section14ExtendedV_one_eq_zero_of_ceil_of_cube_le
    (S : BoundingSieve) {Dnat : ℕ} {y : ℝ}
    (hycube : y ^ 3 ≤ (Dnat : ℝ)) :
    section14ExtendedV S 1 Dnat ⌈y⌉₊ = 0 := by
  classical
  rw [section14ExtendedV_one]
  apply sum_eq_zero
  intro p hp
  have hpynat : p < ⌈y⌉₊ := (mem_filter.mp (mem_filter.mp hp).1).2
  have hpy : (p : ℝ) < y := Nat.lt_ceil.mp hpynat
  have hp3y3 : (p : ℝ) ^ 3 < y ^ 3 := by
    exact pow_lt_pow_left₀ hpy (Nat.cast_nonneg p) (by norm_num)
  have hp3D : (p : ℝ) ^ 3 < (Dnat : ℝ) := hp3y3.trans_le hycube
  have hDlep : Dnat ≤ p ^ 3 := (mem_filter.mp hp).2.2
  have hDlep' : (Dnat : ℝ) ≤ (p : ℝ) ^ 3 := by exact_mod_cast hDlep
  exact False.elim ((not_lt_of_ge hDlep') hp3D)

/-- Exact `section14ExtendedT` recurrence at a ceiling cutoff.  This is the
natural-API form needed at the Case-II endpoint. -/
theorem section14ExtendedT_recurrence_of_ceil_of_cube_le
    (S : BoundingSieve) {N Dnat : ℕ} {y : ℝ} (hN2 : 2 ≤ N)
    (hycube : y ^ 3 ≤ (Dnat : ℝ)) :
    section14ExtendedT S N Dnat ⌈y⌉₊ =
      ∑ p ∈ suzukiSupportedBelow S ⌈y⌉₊,
        S.nu p * section14ExtendedT S (N - 1) (Dnat ⌈/⌉ p) p := by
  apply section14ExtendedT_recurrence S hN2
  intro _
  exact section14ExtendedV_one_eq_zero_of_ceil_of_cube_le S hycube



namespace SwitchingPrinciple.SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers


/-- Exact Case-I endpoint inequality consumed by the Case-II normalized
assembly, transported from the source-faithful parity sum to the natural
`section14ExtendedT` API.  The real endpoint is represented by `ynat = ceil y`,
and the source/extended identification requires the explicit legal-domain
power condition. -/
theorem caseI_source_endpoint_to_caseII_natural
    {S : BoundingSieve} {β s Vz endpointErr y : ℝ}
    {N Dnat ynat : ℕ}
    (hynat : ynat = ⌈y⌉₊)
    (hlegal : ynat ^ N ≤ Dnat)
    (hsourceEndpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n Dnat ynat) ≤
        Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr) :
    section14ExtendedT S N Dnat ynat ≤
      Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr := by
  subst ynat
  rw [← suzukiSourceParitySum_eq_section14ExtendedT_of_pow_le
    S N Dnat ⌈y⌉₊ hlegal]
  exact hsourceEndpoint



end SwitchingPrinciple.SuzukiLemma144KappaOne
end MathlibNt.SieveTheory
