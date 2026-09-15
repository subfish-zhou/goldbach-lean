import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket

open scoped Classical BigOperators
open Filter Finset Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Case-I successor geometry: the first non-automatic edge

This file audits the pointwise-in-`D` hypotheses of the uniform Case-I
successor in their actual order.  The moving source cutoff and both power
cutoffs are automatic, uniformly in every Case-I coordinate `s ≤ σ(D)`.
The next strict source-domain inequality is not automatic at the legal odd
boundary `N = 3, s = 3`; it is therefore frozen as the first genuine premise.
-/

/-- The geometry available before the first strict source-domain premise. -/
structure CaseIPreThresholdGeometryPacket
    (D : ℕ) (d s : ℝ) : Prop where
  hD4 : 4 ≤ D
  hsigma : 1 < sourceSigma (D : ℝ) d
  hpowerSigma : 2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)
  hpowerS : 2 ≤ (D : ℝ) ^ (1 / s)
  hpowerOrder :
    (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (D : ℝ) ^ (1 / s)

/-- A single cutoff depending only on `d` gives all geometry preceding the
strict Section-13 threshold, uniformly in `N` and in every Case-I coordinate
`2 ≤ s ≤ sourceSigma D d`. -/
theorem exists_caseI_preThreshold_geometry_packet
    (d : ℝ) (hd : 1 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧
      ∀ (D _N : ℕ), D0 ≤ (D : ℝ) →
      ∀ s : ℝ, 2 ≤ s → s ≤ sourceSigma (D : ℝ) d →
        CaseIPreThresholdGeometryPacket D d s := by
  obtain ⟨Dσ, hDσ, hσ⟩ :=
    exists_sourceSigma_geometry_threshold d hd
  let D0 : ℝ := max Dσ 4
  refine ⟨D0, hDσ.trans_le (le_max_left _ _), ?_⟩
  intro D N hD s hs hsσ
  have hDσD : Dσ ≤ (D : ℝ) := (le_max_left Dσ 4).trans hD
  have hD4R : (4 : ℝ) ≤ (D : ℝ) := (le_max_right Dσ 4).trans hD
  have hD4 : 4 ≤ D := by exact_mod_cast hD4R
  obtain ⟨hσ3aux, _hroot, hpowσaux⟩ := hσ (D : ℝ) hDσD
  have hσ3 : 3 ≤ sourceSigma (D : ℝ) d := by
    simpa [sourceSigma] using hσ3aux
  have hpowσ : 2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) := by
    simpa [sourceSigma] using hpowσaux
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have horder := rpow_one_div_mono_of_le hD1 hs0 hsσ
  exact {
    hD4 := hD4
    hsigma := (by linarith : 1 < sourceSigma (D : ℝ) d)
    hpowerSigma := hpowσ
    hpowerS := hpowσ.trans horder
    hpowerOrder := horder }

/-- The first premise not supplied by the global IH, parity domains, and the
source contract.  Naming it prevents a chain of pointwise implications from
making the uniform successor vacuous. -/
def CaseIStrictSourceThreshold
    (H : Section13HatLayers) (N : ℕ) (s : ℝ) : Prop :=
  H.betaHat + (ErrorSign.ofDepth N).epsilon < s

/-- `N=3, s=3` is a literal legal parity-boundary point, including the weak
source lower bound used by the uniform `Σ₁₂` theorem. -/
theorem odd_boundary_is_legal_caseI_coordinate :
    (3 : ℝ) ∈ KappaOneModel.parityDomain 2 3 ∧
    (3 : ℝ) - 1 ∈ KappaOneModel.parityDomain 2 (3 - 1) ∧
    2 + (ErrorSign.ofDepth 3).epsilon ≤ (3 : ℝ) := by
  norm_num [KappaOneModel.parityDomain, ErrorSign.ofDepth,
    ErrorSign.epsilon]

/-- At that legal point every source contract has `betaHat = 2`, so the strict
threshold demanded next by the successor is false.  This is a theorem-level
counterexample to deriving the threshold from the advertised inputs. -/
theorem odd_boundary_does_not_supply_strict_source_threshold
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ¬ CaseIStrictSourceThreshold H 3 3 := by
  rw [CaseIStrictSourceThreshold, hH.betaHat_eq]
  norm_num [ErrorSign.ofDepth, ErrorSign.epsilon]

/-- The subsequent odd cubic condition is independently non-automatic for a
natural ceiling: at `D=2, s=3`, the ceiling is `2`, whose cube exceeds `D`.
Thus even strengthening the first strict edge would not justify silently
manufacturing `z^3 ≤ D` from ceiling geometry. -/
theorem odd_natCeil_cubic_condition_not_automatic :
    let z := ⌈((2 : ℕ) : ℝ) ^ (1 / (3 : ℝ))⌉₊
    ¬ z ^ 3 ≤ 2 := by
  dsimp only
  let z : ℕ := ⌈((2 : ℕ) : ℝ) ^ (1 / (3 : ℝ))⌉₊
  obtain ⟨_hlower, hupper⟩ := natCeil_cuberoot_cubeBracket 2 (by omega)
  change ¬ z ^ 3 ≤ 2
  change 2 ≤ z ^ 3 at hupper
  have hz2 : 2 ≤ z := by
    by_contra h
    have hz : z ≤ 1 := by omega
    interval_cases z <;> norm_num at hupper
  have h8 : 8 ≤ z ^ 3 := by
    norm_num [pow_succ]
    nlinarith
  omega


end MathlibNt.SieveTheory
