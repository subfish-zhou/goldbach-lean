/-
A finite, source-indexed discrete Suzuki package.

`section14ExtendedV S n D z` is a total extension of the recurrence used only after
Section 14 support/domain reductions.  It is not Suzuki’s unconditional `V_n`.
It is indexed by the length `n` of the complete source
chain.  Its base `n = 1` is Suzuki's terminal cubic shell.  For `n >= 2` the
definition is the exact one-prime recurrence of Lemma 7.1, with natural levels
represented by `Nat.ceilDiv`: `D/p` in the source becomes `D ⌈/⌉ p`, preserving
strict integral inequalities.

`section14ExtendedT S N D z` is project notation for Suzuki's finite discrete
parity sum; Suzuki uses `T_N(D,z)` in Lemma 14.4 but reserves the displayed
Section 9 notation for its continuous counterpart.
-/
import MathlibNt.SieveTheory.LowerSuzukiDiscreteBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The finite Euler product `V(z)` on the supported prime carrier. -/
noncomputable def sourceDiscreteEuler (S : BoundingSieve) (z : ℕ) : ℝ :=
  ∏ p ∈ suzukiSupportedBelow S z, (1 - S.nu p)

/-- Suzuki's discrete `V_n(D,z)`, with complete-chain source index `n`.

At `n=1` this is exactly the one-prime terminal shell
`p < D ∧ D ≤ p^3`.  For `n+2`, peeling the largest source prime gives the
source recurrence with level `D/p`, encoded exactly on naturals by
`D ⌈/⌉ p`.  Index zero is deliberately zero: it is not a source layer. -/
noncomputable def section14ExtendedV (S : BoundingSieve) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | 1, D, z =>
      ∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p => p < D ∧ D ≤ p ^ 3),
        S.nu p * sourceDiscreteEuler S p
  | n + 2, D, z =>
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * section14ExtendedV S (n + 1) (D ⌈/⌉ p) p

@[simp] theorem section14ExtendedV_zero (S : BoundingSieve) (D z : ℕ) :
    section14ExtendedV S 0 D z = 0 := rfl

@[simp] theorem section14ExtendedV_one (S : BoundingSieve) (D z : ℕ) :
    section14ExtendedV S 1 D z =
      ∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p => p < D ∧ D ≤ p ^ 3),
        S.nu p * sourceDiscreteEuler S p := rfl

/-- Exact one-prime source recurrence, valid for every positive predecessor
index.  No positivity or analytic hypothesis is used. -/
theorem section14ExtendedV_succ_of_pos
    (S : BoundingSieve) {n : ℕ} (hn : 0 < n) (D z : ℕ) :
    section14ExtendedV S (n + 1) D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * section14ExtendedV S n (D ⌈/⌉ p) p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rfl

/-- Exact support boundary for the exceptional source layer `V₁`.  This is the
finite form used in Suzuki's Case I when `s ≥ β+1` and `β=2`: `z^3 ≤ D`. -/
theorem section14ExtendedV_one_eq_zero_of_cube_le
    (S : BoundingSieve) {D z : ℕ} (hzD : z ^ 3 ≤ D) :
    section14ExtendedV S 1 D z = 0 := by
  classical
  rw [section14ExtendedV_one]
  apply sum_eq_zero
  intro p hp
  have hmem := mem_filter.mp hp
  have hpz : p < z := (mem_filter.mp hmem.1).2
  have hp3z3 : p ^ 3 < z ^ 3 := Nat.pow_lt_pow_left hpz (by norm_num)
  omega

/-- Source-selected indices `1 ≤ n ≤ N`, `n ≡ N (mod 2)`. -/
def sourceParityIndices (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => n % 2 = N % 2)

/-- The positive-index tail, used to separate the exceptional `V₁` term. -/
def sourceParityTailIndices (N : ℕ) : Finset ℕ :=
  (Icc 2 N).filter (fun n => n % 2 = N % 2)

/-- The finite discrete parity sum `T_N(D,z)`. -/
noncomputable def section14ExtendedT
    (S : BoundingSieve) (N D z : ℕ) : ℝ :=
  ∑ n ∈ sourceParityIndices N, section14ExtendedV S n D z

@[simp] theorem section14ExtendedT_zero (S : BoundingSieve) (D z : ℕ) :
    section14ExtendedT S 0 D z = 0 := by
  simp [section14ExtendedT, sourceParityIndices]

private theorem sourceParityIndices_eq_tail_of_even
    {N : ℕ} (hN : Even N) :
    sourceParityIndices N = sourceParityTailIndices N := by
  ext n
  simp only [sourceParityIndices, sourceParityTailIndices, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hpar⟩
    have hNmod : N % 2 = 0 := Nat.even_iff.mp hN
    have hnmod : n % 2 = 0 := hpar.trans hNmod
    have hn2 : 2 ≤ n := by omega
    exact ⟨⟨hn2, hnN⟩, hpar⟩
  · rintro ⟨⟨hn2, hnN⟩, hpar⟩
    exact ⟨⟨by omega, hnN⟩, hpar⟩

private theorem sourceParityIndices_eq_insert_one_tail_of_odd
    {N : ℕ} (hN : Odd N) :
    sourceParityIndices N = insert 1 (sourceParityTailIndices N) := by
  ext n
  simp only [sourceParityIndices, sourceParityTailIndices, mem_filter, mem_Icc,
    mem_insert]
  have hN1 : 1 ≤ N := by
    obtain ⟨k, hk⟩ := hN
    omega
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hpar⟩
    by_cases hn : n = 1
    · exact Or.inl hn
    · exact Or.inr ⟨⟨by omega, hnN⟩, hpar⟩
  · rintro (rfl | ⟨⟨hn2, hnN⟩, hpar⟩)
    · exact ⟨⟨le_rfl, hN1⟩, by simpa using (Nat.odd_iff.mp hN).symm⟩
    · exact ⟨⟨by omega, hnN⟩, hpar⟩

private theorem sum_sourceParityTail_eq_shift
    (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ sourceParityTailIndices (N + 1), f n =
      ∑ m ∈ sourceParityIndices N, f (m + 1) := by
  classical
  apply Finset.sum_bij (fun n _ => n - 1)
  · intro n hn
    simp only [sourceParityTailIndices, mem_filter, mem_Icc] at hn
    simp only [sourceParityIndices, mem_filter, mem_Icc]
    constructor
    · omega
    · omega
  · intro a ha b hb hab
    simp only [sourceParityTailIndices, mem_filter, mem_Icc] at ha hb
    omega
  · intro m hm
    simp only [sourceParityIndices, mem_filter, mem_Icc] at hm
    refine ⟨m + 1, ?_, ?_⟩
    · simp only [sourceParityTailIndices, mem_filter, mem_Icc]
      constructor
      · omega
      · omega
    · omega
  · intro n hn
    simp only [sourceParityTailIndices, mem_filter, mem_Icc] at hn
    congr 1
    omega

/-- Exact parity recurrence for even source cutoff `N`.  Since every selected
index is at least two, no terminal boundary term occurs. -/
theorem section14ExtendedT_recurrence_of_even
    (S : BoundingSieve) {N D z : ℕ} (hN : Even N) (hN2 : 2 ≤ N) :
    section14ExtendedT S N D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * section14ExtendedT S (N - 1) (D ⌈/⌉ p) p := by
  classical
  have hNm : N - 1 + 1 = N := by omega
  rw [section14ExtendedT, sourceParityIndices_eq_tail_of_even hN]
  rw [← hNm, sum_sourceParityTail_eq_shift]
  apply Eq.trans (Finset.sum_congr rfl (fun m hm =>
    section14ExtendedV_succ_of_pos S (by
      simp only [sourceParityIndices, mem_filter, mem_Icc] at hm
      omega) D z))
  rw [Finset.sum_comm]
  unfold section14ExtendedT
  simp_rw [Finset.mul_sum]
  congr 3

/-- For odd `N`, the only obstruction to the same recurrence is the source
base layer `V₁`; all higher selected layers reindex exactly. -/
theorem section14ExtendedT_eq_one_add_recurrence_of_odd
    (S : BoundingSieve) {N D z : ℕ} (hN : Odd N) (hN1 : 1 ≤ N) :
    section14ExtendedT S N D z = section14ExtendedV S 1 D z +
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * section14ExtendedT S (N - 1) (D ⌈/⌉ p) p := by
  classical
  have hNm : N - 1 + 1 = N := by omega
  rw [section14ExtendedT, sourceParityIndices_eq_insert_one_tail_of_odd hN]
  rw [sum_insert]
  · rw [← hNm, sum_sourceParityTail_eq_shift]
    congr 1
    apply Eq.trans (Finset.sum_congr rfl (fun m hm =>
      section14ExtendedV_succ_of_pos S (by
        simp only [sourceParityIndices, mem_filter, mem_Icc] at hm
        omega) D z))
    rw [Finset.sum_comm]
    unfold section14ExtendedT
    simp_rw [Finset.mul_sum]
    congr 3
  · simp only [sourceParityTailIndices, mem_filter, mem_Icc]
    omega

/-- Suzuki Case-I exact recurrence.  For even `N` it is unconditional; for odd
`N`, the precise boundary hypothesis is the vanishing of `V₁(D,z)`. -/
theorem section14ExtendedT_recurrence
    (S : BoundingSieve) {N D z : ℕ} (hN2 : 2 ≤ N)
    (hboundary : Odd N → section14ExtendedV S 1 D z = 0) :
    section14ExtendedT S N D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * section14ExtendedT S (N - 1) (D ⌈/⌉ p) p := by
  rcases Nat.even_or_odd N with hN | hN
  · exact section14ExtendedT_recurrence_of_even S hN hN2
  · rw [section14ExtendedT_eq_one_add_recurrence_of_odd S hN (by omega), hboundary hN,
      zero_add]

/-- The concrete Case-I boundary `z^3 ≤ D` kills `V₁`, hence yields the exact
recurrence for both parities. -/
theorem section14ExtendedT_recurrence_of_cube_le
    (S : BoundingSieve) {N D z : ℕ} (hN2 : 2 ≤ N) (hzD : z ^ 3 ≤ D) :
    section14ExtendedT S N D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * section14ExtendedT S (N - 1) (D ⌈/⌉ p) p := by
  apply section14ExtendedT_recurrence S hN2
  intro _
  exact section14ExtendedV_one_eq_zero_of_cube_le S hzD

/-- The normalized lower `V_n(D,z)/V(z)` written directly on the production
lower-boundary chain carrier.  The terminal prime `q` is external to `l`, so
the complete source index is imposed by `l.length + 1 = n`. -/
noncomputable def sourceDiscreteLowerBoundaryV
    (S : BoundingSieve) (n D z : ℕ) : ℝ :=
  ∑ q ∈ suzukiSupportedBelow S z,
    S.nu q * suzukiSuffixRatio S z q *
      ∑ l ∈ lowerRosserBoundaryChainsAtSourceIndex D q
          ((suzukiSupportedBelow S z).filter (fun p => q < p)) n,
        (l.map S.nu).prod

/-- The recursive source layer at index two, fully expanded.  This is the
strongest unconditional comparison datum with the lower boundary carrier: its
inner terminal shell is tested at the divided level `D ⌈/⌉ p`. -/
theorem section14ExtendedV_two_eq_recursiveCarrier
    (S : BoundingSieve) (D z : ℕ) :
    section14ExtendedV S 2 D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p *
          ∑ q ∈ (suzukiSupportedBelow S p).filter
              (fun q => q < D ⌈/⌉ p ∧ D ⌈/⌉ p ≤ q ^ 3),
            S.nu q * sourceDiscreteEuler S q := by
  rfl

/-- The chain-based lower slice at index two, fully expanded.  In contrast to
`section14ExtendedV_two_eq_recursiveCarrier`, the stored prime is tested by
`p < D`, while the terminal prime `q` occurs only in the cubic crossing test
`D ≤ p*q^3`.  Thus the two definitions do not have the same base carrier. -/
theorem sourceDiscreteLowerBoundaryV_two_eq_chainCarrier
    (S : BoundingSieve) (D z : ℕ) :
    sourceDiscreteLowerBoundaryV S 2 D z =
      ∑ q ∈ suzukiSupportedBelow S z,
        S.nu q * suzukiSuffixRatio S z q *
          ∑ p ∈ ((suzukiSupportedBelow S z).filter (fun p => q < p)).filter
              (fun p => p < D ∧ D ≤ p * q ^ 3),
            S.nu p := by
  classical
  unfold sourceDiscreteLowerBoundaryV
  apply sum_congr rfl
  intro q hq
  let P := (suzukiSupportedBelow S z).filter (fun p => q < p)
  have hqS : q ∈ S.prodPrimes.primeFactors := (mem_filter.mp hq).1
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqS
  have hqnot : q ∉ P := by simp [P]
  have hqmin : ∀ p ∈ P, q ≤ p := by
    intro p hp
    exact (mem_filter.mp hp).2.le
  have hinner :
      (∑ l ∈ lowerRosserBoundaryChainsAtSourceIndex D q P 2,
          (l.map S.nu).prod) =
        ∑ p ∈ P.filter (fun p => p < D ∧ D ≤ p * q ^ 3), S.nu p := by
    rw [← lowerRosserBoundaryChainsFixedPairDepth0Density_zero_eq_sourceIndex_two]
    exact lowerRosserBoundaryChainsFixedPairDepth0Density_zero
      S.nu hqnot hqprime hqmin
  simp [P, hinner]

/-- The base carriers are genuinely different, already on prime-shaped data:
with stored prime `p = 5`, terminal prime `q = 2`, and level `D = 9`, the
chain predicate holds but the recursive divided-level predicate does not. -/
theorem sourceDiscrete_two_base_predicates_not_equivalent :
    ¬ ((2 < 9 ⌈/⌉ 5 ∧ 9 ⌈/⌉ 5 ≤ 2 ^ 3) ↔
      (5 < 9 ∧ 9 ≤ 5 * 2 ^ 3)) := by
  norm_num

/-- A lower-boundary source slice is supported only at even complete-chain
indices. -/
theorem sourceDiscreteLowerBoundaryV_eq_zero_of_odd
    (S : BoundingSieve) {n D z : ℕ} (hn : Odd n) :
    sourceDiscreteLowerBoundaryV S n D z = 0 := by
  classical
  unfold sourceDiscreteLowerBoundaryV
  apply sum_eq_zero
  intro q hq
  have hinner :
      (∑ l ∈ lowerRosserBoundaryChainsAtSourceIndex D q
          ((suzukiSupportedBelow S z).filter (fun p => q < p)) n,
        (l.map S.nu).prod) = 0 := by
    apply sum_eq_zero
    intro l hl
    exact False.elim ((Nat.not_even_iff_odd.mpr hn)
      (even_sourceIndex_of_mem_lowerRosserBoundaryChainsAtSourceIndex hl))
  rw [hinner, mul_zero]

/-- Exact identification of the direct source-index slice with the existing
production lower layer at source index `2*k+2`. -/
theorem sourceDiscreteLowerBoundaryV_even_eq_normalizedLayer
    (S : BoundingSieve) (D z k : ℕ) :
    sourceDiscreteLowerBoundaryV S (2 * k + 2) D z =
      lowerSuzukiNormalizedLayer S D 0 z k := by
  classical
  unfold sourceDiscreteLowerBoundaryV
  rw [lowerSuzukiNormalizedLayer_eq_primeSum]
  simp only [Nat.zero_le, filter_true]
  apply sum_congr rfl
  intro q hq
  rw [lowerSuzukiDiscreteKernel_sourceIndex]

/-- Existing lower Rosser preterminal chains carry the exact complete-chain
source index: odd stored length `2k+1`, plus the external terminal prime, is
`2k+2`.  This is the non-proxy bridge used by the lower discrete layer. -/
theorem sourceDiscrete_lower_boundary_index
    (S : BoundingSieve) (D z k q : ℕ) :
    lowerSuzukiDiscreteKernel S D z k q =
      ∑ l ∈ lowerRosserBoundaryChainsAtSourceIndex D q
          ((suzukiSupportedBelow S z).filter (fun p => q < p)) (2 * k + 2),
        (l.map S.nu).prod :=
  lowerSuzukiDiscreteKernel_sourceIndex S D z k q

/-- Every chain in the lower slice has even complete source index. -/
theorem sourceDiscrete_lower_boundary_even
    {D q n : ℕ} {P : Finset ℕ} {l : List ℕ}
    (hl : l ∈ lowerRosserBoundaryChainsAtSourceIndex D q P n) : Even n :=
  even_sourceIndex_of_mem_lowerRosserBoundaryChainsAtSourceIndex hl


end MathlibNt.SieveTheory
