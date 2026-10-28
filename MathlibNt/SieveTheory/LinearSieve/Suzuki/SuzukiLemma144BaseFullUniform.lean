import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ComparisonInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SigmaTwoZeroKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146iErrorEnvelopeTransport

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Above the initial strip, the depth-one continuous source layer vanishes. -/
theorem finiteSourceLayer_one_eq_zero_of_three_le
    {s : ℝ} (hs3 : 3 ≤ s) :
    finiteSourceLayer 1 2 1 s = 0 := by
  simp [finiteSourceLayer, suzukiLayer, baseLower, dPowDensity,
    intervalIntegral.integral_const]
  norm_num at hs3 ⊢
  rw [min_eq_right hs3]
  ring
  exact Or.inr trivial

/-- At a power cutoff with exponent strictly above three, the actual depth-one
source is empty: every natural below the cutoff has cube strictly below `D`. -/
theorem suzukiActualT_one_natCeil_eq_zero_of_three_lt
    (S : BoundingSieve) {D : ℕ} {s : ℝ}
    (hD : 1 ≤ D) (hs3 : 3 < s) :
    suzukiActualT S 1 D ⌈(D : ℝ) ^ (1 / s)⌉₊ = 0 := by
  rw [suzukiActualT_one]
  apply suzukiSourceV_one_eq_zero_of_cube_lt_below
  intro p hp
  have hDreal : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hs0 : 0 < (3 : ℝ) := by norm_num
  have hcut : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 / 3 : ℝ) :=
    rpow_one_div_mono_of_le hDreal hs0 hs3.le
  have hroot0 : 0 < (D : ℝ) ^ (1 / s) := by positivity
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / s) := by
    rw [← Nat.lt_ceil]
    exact hp
  have hpCubeRoot : (p : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) :=
    hpRoot.trans_le hcut
  by_cases hp0 : p = 0
  · subst p
    simp
    omega
  have hpReal0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hp0)
  have hDpos : 0 < (D : ℝ) := lt_of_lt_of_le zero_lt_one hDreal
  have hr := Real.lt_rpow_inv_iff_of_pos
    (x := (p : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
    hpReal0.le hDpos.le (by norm_num)
  norm_num [one_div] at hr
  have hpCubeReal : (p : ℝ) ^ (3 : ℕ) < (D : ℝ) := hr.mp hpCubeRoot
  exact_mod_cast hpCubeReal


end MathlibNt.SieveTheory
