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









end MathlibNt.SieveTheory
