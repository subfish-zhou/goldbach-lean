import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIINaturalCutoff
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVnSemanticResolution

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- A natural-number formulation of the source cutoff `y = D^(1/3)` on the
finite prime support relevant below `z`.  It records the exact strict-cutoff
statement used in Suzuki Case II, without imposing either incompatible rounded
cube inequality on `y`. -/
def SuzukiSourceCubeCut
    (S : BoundingSieve) (D y z : ℕ) : Prop :=
  ∀ p ∈ suzukiSupportedBelow S z, (p < y ↔ p ^ 3 < D)

/-- The standard natural encoding of Suzuki's real cutoff `D^(1/3)` implies
its exact strict membership rule.  Thus `y` is the ceiling cube root: the last
integer below the real cutoff is `y-1`. -/
theorem suzukiSourceCubeCut_of_ceilingCube
    (S : BoundingSieve) {D y z : ℕ}
    (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3) :
    SuzukiSourceCubeCut S D y z := by
  intro p _
  constructor
  · intro hpy
    have hp : p ≤ y - 1 := by omega
    have hpow : p ^ 3 ≤ (y - 1) ^ 3 := Nat.pow_le_pow_left hp 3
    omega
  · intro hpD
    by_contra hpy
    have hyp : y ≤ p := Nat.le_of_not_gt hpy
    have hpow : y ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hyp 3
    omega

/-- The source base layer vanishes below the cubic cutoff. -/
theorem suzukiSourceV_one_eq_zero_of_cubeCut
    (S : BoundingSieve) {D y z : ℕ} (hyz : y ≤ z)
    (hcut : SuzukiSourceCubeCut S D y z) :
    suzukiSourceV S 1 D y = 0 := by
  classical
  rw [suzukiSourceV_one]
  apply sum_eq_zero
  intro p hp
  have hp' := mem_filter.mp hp
  have hpy : p ∈ suzukiSupportedBelow S y := hp'.1
  have hpz : p ∈ suzukiSupportedBelow S z := by
    simp only [suzukiSupportedBelow, mem_filter] at hpy ⊢
    exact ⟨hpy.1, hpy.2.trans_le hyz⟩
  have hp3 : p ^ 3 < D := (hcut p hpz).mp ((mem_filter.mp hpy).2)
  exact False.elim ((Nat.not_lt_of_ge hp'.2) hp3)

/-- Every odd source layer of index at least three is unchanged when its outer
cutoff is enlarged from the cubic cutoff `y` to `z`.  This is immediate from
Suzuki's literal odd-index carrier `p^3 < D`; no global hypothesis `z^n ≤ D`
is involved. -/
theorem suzukiSourceV_eq_of_cubeCut_of_odd
    (S : BoundingSieve) {n D y z : ℕ} (hn2 : 2 ≤ n) (hn : Odd n)
    (hyz : y ≤ z) (hcut : SuzukiSourceCubeCut S D y z) :
    suzukiSourceV S n D z = suzukiSourceV S n D y := by
  classical
  have hpred : 0 < n - 1 := by omega
  have hnrepr : n - 1 + 1 = n := by omega
  rw [← hnrepr, suzukiSourceV_succ_of_pos S hpred,
    suzukiSourceV_succ_of_pos S hpred]
  apply sum_congr
  · ext p
    simp only [suzukiSourceOuterCarrier, mem_filter]
    constructor
    · rintro ⟨⟨hpP, hpzlt⟩, hlower, hupper⟩
      have hpz : p ∈ suzukiSupportedBelow S z := by
        exact mem_filter.mpr ⟨hpP, hpzlt⟩
      have hp3 : p ^ 3 < D := hupper (by simpa [hnrepr] using hn)
      exact ⟨⟨hpP, (hcut p hpz).mpr hp3⟩, hlower, hupper⟩
    · rintro ⟨⟨hpP, hpylt⟩, hlower, hupper⟩
      exact ⟨⟨hpP, hpylt.trans_le hyz⟩, hlower, hupper⟩
  · intro p hp
    rfl

/-- Source-faithful Case-II cutoff identity (Suzuki (14.24), at `β = 2`).

The selected indices are odd.  The `n=1` layer vanishes at the natural cubic
cutoff, while every selected `n≥3` layer has Suzuki's own outer carrier
`p^3<D`, hence is already supported below `y`.  In particular this proof does
not pass through `section14ExtendedV` and does not assume the false-for-`N>3`
global bridge `z^N ≤ D`. -/
theorem suzukiSourceParitySum_caseII_cut
    (S : BoundingSieve) {N D y z : ℕ} (hN : Odd N) (hyz : y ≤ z)
    (hcut : SuzukiSourceCubeCut S D y z) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) +
        suzukiSourceV S 1 D z := by
  classical
  have hN1 : 1 ≤ N := by
    obtain ⟨k, rfl⟩ := hN
    omega
  have hNmod : N % 2 = 1 := Nat.odd_iff.mp hN
  have hone : 1 ∈ sourceParityIndices N := by
    simp [sourceParityIndices, hN1, hNmod]
  have hbase : suzukiSourceV S 1 D y = 0 :=
    suzukiSourceV_one_eq_zero_of_cubeCut S hyz hcut
  rw [← Finset.sum_erase_add _ _ hone, ← Finset.sum_erase_add _ _ hone]
  rw [hbase, add_zero]
  have htail :
      (∑ n ∈ (sourceParityIndices N).erase 1, suzukiSourceV S n D z) =
        ∑ n ∈ (sourceParityIndices N).erase 1, suzukiSourceV S n D y := by
    apply sum_congr rfl
    intro n hnmem
    have hnsel : n ∈ sourceParityIndices N := mem_of_mem_erase hnmem
    have hn1 : n ≠ 1 := ne_of_mem_erase hnmem
    have hnbounds : 1 ≤ n ∧ n ≤ N := by
      exact mem_Icc.mp (mem_filter.mp hnsel).1
    have hnodd : Odd n := by
      rw [Nat.odd_iff]
      exact (mem_filter.mp hnsel).2.trans hNmod
    exact suzukiSourceV_eq_of_cubeCut_of_odd S (by omega) hnodd hyz hcut
  rw [htail]

/-- (14.24) with the natural hypotheses expressing `y = D^(1/3)` for strict
integer prime cutoffs. -/
theorem suzukiSourceParitySum_caseII_cut_of_ceilingCube
    (S : BoundingSieve) {N D y z : ℕ} (hN : Odd N) (hyz : y ≤ z)
    (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) +
        suzukiSourceV S 1 D z :=
  suzukiSourceParitySum_caseII_cut S hN hyz
    (suzukiSourceCubeCut_of_ceilingCube S hyLower hyUpper)


end MathlibNt.SieveTheory
