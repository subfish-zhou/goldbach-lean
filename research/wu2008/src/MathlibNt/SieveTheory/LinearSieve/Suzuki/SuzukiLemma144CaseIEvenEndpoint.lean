import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-!
# Lemma 14.4, Case I: the even lower endpoint `s = 2`

When the successor depth `M` is even, the formal predecessor endpoint `1` is
not in the open odd parity domain.  It is nevertheless not an index of the
actual finite recurrence: every summand has `p < D^(1/2)`, hence its inherited
coordinate `log D / log p - 1` is strictly larger than `1`.

Thus the endpoint is a strict-carrier boundary phenomenon.  The actual
natural-ceiling recurrence remains exact, and both coordinates used by the
induction hypothesis lie in the predecessor parity domain.  No estimate for
the desired Lemma-14.4 conclusion is assumed below.
-/

private theorem inheritedCoordinate_gt_one_of_lt_sqrt
    {D p : ℕ} (hp : 2 ≤ p) (hD : 1 < D)
    (hupper : (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ))) :
    1 < inheritedCoordinate D p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hloglt := Real.strictMonoOn_log
    (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
    (show (D : ℝ) ^ (1 / (2 : ℝ)) ∈ Set.Ioi 0 by
      exact Real.rpow_pos_of_pos hDR _)
    hupper
  rw [Real.log_rpow hDR] at hloglt
  unfold inheritedCoordinate
  have : (2 : ℝ) < Real.log (D : ℝ) / Real.log (p : ℝ) := by
    rw [lt_div_iff₀ hlogp]
    norm_num [one_div] at hloglt ⊢
    nlinarith
  linarith

/-- At even depth the odd source-cutoff premise of the exact recurrence is
vacuous.  Therefore `suzukiActualT_caseI_recurrence_strict` applies at the
literal natural ceiling without any (generally false) ceiling-square claim. -/
theorem lemma144_caseI_even_endpoint_odd_carrier
    {M D z : ℕ} (hM : Even M) :
    Odd M → ∀ p < z, p ^ 3 < D := by
  intro hOdd
  exact False.elim ((Nat.not_even_iff_odd.mpr hOdd) hM)

/-- Every actual recurrence index at the even endpoint has inherited
coordinate strictly inside the predecessor's open odd parity domain.  This is
the strict inequality which the formal endpoint `2 - 1 = 1` itself lacks. -/
theorem lemma144_caseI_even_endpoint_inherited_domain
    (S : BoundingSieve) {M D z : ℕ}
    (hM : Even M) (hM2 : 2 ≤ M) (hD : 4 ≤ D)
    (hz : z = ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) :
    ∀ p ∈ SwitchingPrinciple.suzukiSupportedBelow S z,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hrootPos : 0 < (D : ℝ) ^ (1 / (2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) :=
    (nat_lt_natCeil_iff_lt_real hrootPos hz).1 hp'.2
  have hcoord : 1 < inheritedCoordinate D p :=
    inheritedCoordinate_gt_one_of_lt_sqrt hpPrime.two_le (by omega) hpRoot
  have hMmod : M % 2 = 0 := Nat.even_iff.mp hM
  have hpredOdd : (M - 1) % 2 = 1 := by omega
  simp only [KappaOneModel.parityDomain, hpredOdd, if_pos, Set.mem_Ioi]
  norm_num
  exact hcoord

/-- The ceiling-recursive coordinate is also legal, and Proposition 9.3 gives
exactly the finite-source-layer comparison needed by the pointwise IH.  This
uniform packet uses only actual recurrence indices; it has no hypothesis that
`1` belongs to the predecessor parity domain. -/
theorem lemma144_caseI_even_endpoint_source_packet
    (S : BoundingSieve) {M D z : ℕ}
    (hM : Even M) (hM2 : 2 ≤ M) (hD : 4 ≤ D)
    (hz : z = ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) :
    ∀ p ∈ SwitchingPrinciple.suzukiSupportedBelow S z,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) ∧
      finiteSourceLayer 1 2 (M - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (M - 1) (inheritedCoordinate D p) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hrootPos : 0 < (D : ℝ) ^ (1 / (2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) :=
    (nat_lt_natCeil_iff_lt_real hrootPos hz).1 hp'.2
  have hpSquareR : (p : ℝ) ^ (2 : ℕ) < (D : ℝ) := by
    have hiff := Real.lt_rpow_inv_iff_of_pos
      (x := (p : ℝ)) (y := (D : ℝ)) (z := (2 : ℝ))
      (by positivity) (by positivity) (by norm_num)
    norm_num [one_div] at hiff hpRoot ⊢
    exact hiff.mp hpRoot
  have hpSquare : p ^ 2 < D := by exact_mod_cast hpSquareR
  have h2p : 2 * p ≤ D := by
    have : 2 * p ≤ p ^ 2 := by nlinarith [hpPrime.two_le]
    omega
  have hinherited := lemma144_caseI_even_endpoint_inherited_domain S hM hM2 hD hz p hp
  have hrecursive : recursiveCoordinate D p ∈
      KappaOneModel.parityDomain 2 (M - 1) :=
    parityDomain_mono hinherited (coordinate_bounds hpPrime.two_le h2p).1
  refine ⟨hinherited, hrecursive, ?_⟩
  exact finiteSourceLayer_recursive_le_inherited (by norm_num) (M - 1) D p
    hpPrime.two_le h2p hinherited hrecursive


end MathlibNt.SieveTheory
