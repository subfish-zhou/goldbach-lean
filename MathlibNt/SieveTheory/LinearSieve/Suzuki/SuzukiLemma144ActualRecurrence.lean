import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVnSemanticResolution
import Mathlib.Algebra.Order.Floor.Div

/-!
# Suzuki Lemma 14.4: the actual discrete recurrence and (14.9)

This file works with the source-faithful natural-valued layers `suzukiSourceV`.
The quotient in every recursive layer is therefore literally `D ⌈/⌉ p`.
-/

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

/-- The actual finite parity aggregate: `V_N + V_{N-2} + ...`, stopping at
`V₁` or `V₂`.  In particular depth zero is not inserted into a positive-depth
Suzuki sum. -/
noncomputable def suzukiActualT (S : BoundingSieve) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | 1, D, z => suzukiSourceV S 1 D z
  | n + 2, D, z => suzukiSourceV S (n + 2) D z + suzukiActualT S n D z

@[simp] theorem suzukiActualT_zero (S : BoundingSieve) (D z : ℕ) :
    suzukiActualT S 0 D z = 0 := rfl

@[simp] theorem suzukiActualT_one (S : BoundingSieve) (D z : ℕ) :
    suzukiActualT S 1 D z = suzukiSourceV S 1 D z := rfl

@[simp] theorem suzukiActualT_add_two (S : BoundingSieve) (n D z : ℕ) :
    suzukiActualT S (n + 2) D z =
      suzukiSourceV S (n + 2) D z + suzukiActualT S n D z := rfl

/-- The literal finite carrier `1 ≤ n ≤ N`, `n ≡ N (mod 2)`. -/
def suzukiActualParityCarrier (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n => 1 ≤ n ∧ n % 2 = N % 2

/-- The recursive presentation above is exactly Suzuki's displayed finite
parity sum, not an unbounded series or a depth scan. -/
theorem suzukiActualT_eq_parity_sum (S : BoundingSieve) (N D z : ℕ) :
    suzukiActualT S N D z =
      ∑ n ∈ suzukiActualParityCarrier N, suzukiSourceV S n D z := by
  induction N using Nat.twoStepInduction with
  | zero =>
      symm
      apply Finset.sum_eq_zero
      intro n hn
      simp [suzukiActualParityCarrier] at hn
      omega
  | one =>
      have hc : suzukiActualParityCarrier 1 = {1} := by
        ext n
        simp [suzukiActualParityCarrier]
        omega
      rw [hc]
      simp
  | more n ih ih1 =>
      rw [suzukiActualT_add_two, ih]
      simp only [suzukiActualParityCarrier, Finset.sum_filter,
        Finset.sum_range_succ]
      have hsame : (n + 2) % 2 = n % 2 := by omega
      have hflip : (n + 1) % 2 ≠ n % 2 := by omega
      simp [hsame, hflip]
      ring

/-- The elementary support cutoff used to erase Suzuki's lower outer cutoff.
It includes the natural boundary with `≤`: strictness comes from `p < z`. -/
theorem suzukiSourceV_eq_zero_of_pow_le_allDepth
    (S : BoundingSieve) (n D z : ℕ) (hzD : z ^ (n + 2) ≤ D) :
    suzukiSourceV S n D z = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero =>
          rw [suzukiSourceV_one]
          apply Finset.sum_eq_zero
          intro p hp
          simp only [Finset.mem_filter] at hp
          rcases hp with ⟨hpSupport, hDp⟩
          have hpSupport' :
              (p ∈ S.prodPrimes.primeFactors) ∧ p < z := by
            simpa [suzukiSupportedBelow] using hpSupport
          have hpz : p < z := hpSupport'.2
          have hpow : p ^ 3 < z ^ 3 := Nat.pow_lt_pow_left hpz (by omega)
          have hzD' : z ^ 3 ≤ D := by simpa using hzD
          exfalso
          exact (not_lt_of_ge hDp) (hpow.trans_le hzD')
      | succ n =>
          rw [suzukiSourceV_succ_of_pos S (by omega : 0 < n + 1)]
          apply Finset.sum_eq_zero
          intro p hp
          simp only [suzukiSourceOuterCarrier, Finset.mem_filter] at hp
          rcases hp with ⟨⟨hpP, hpz⟩, hDp, _⟩
          have hpow : p ^ ((n + 2) + 2) < z ^ ((n + 2) + 2) :=
            Nat.pow_lt_pow_left hpz (by omega)
          have hzD' : z ^ ((n + 2) + 2) ≤ D := by
            convert hzD using 1 <;> omega
          exfalso
          exact (not_lt_of_ge hDp) (hpow.trans_le hzD')

/-- For a positive predecessor, the lower carrier may be erased by support
vanishing.  In odd outer depth the Case-I boundary `z³ ≤ D` also makes the
source upper cutoff automatic. -/
theorem suzukiSourceV_succ_eq_unrestricted
    (S : BoundingSieve) {n D z : ℕ} (hn : 0 < n)
    (hOddBoundary : Odd (n + 1) → z ^ 3 ≤ D) :
    suzukiSourceV S (n + 1) D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiSourceV S n (D ⌈/⌉ p) p := by
  rw [suzukiSourceV_succ_of_pos S hn]
  apply Finset.sum_subset
  · intro p hp
    simp only [suzukiSourceOuterCarrier, Finset.mem_filter] at hp
    simpa [suzukiSupportedBelow] using hp.1
  · intro p hpSupport hpNotCarrier
    have hpSupport' :
        (p ∈ S.prodPrimes.primeFactors) ∧ p < z := by
      simpa [suzukiSupportedBelow] using hpSupport
    have hpz : p < z := hpSupport'.2
    have hpPrime : Nat.Prime p := by
      apply Nat.prime_of_mem_primeFactors
      exact hpSupport'.1
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hp0 : 0 < p := by omega
    have hUpper : Odd (n + 1) → p ^ 3 < D := by
      intro hodd
      have hpz3 : p ^ 3 < z ^ 3 := Nat.pow_lt_pow_left hpz (by omega)
      exact hpz3.trans_le (hOddBoundary hodd)
    have hLowerFails : ¬ D ≤ p ^ ((n + 1) + 2) := by
      intro hLower
      apply hpNotCarrier
      simp only [suzukiSourceOuterCarrier, Finset.mem_filter]
      exact ⟨⟨hpSupport'.1, hpz⟩,
        hLower, hUpper⟩
    have hpowD : p ^ (n + 3) < D := by
      have := Nat.lt_of_not_ge hLowerFails
      convert this using 1 <;> omega
    have hDceil : D ≤ p * (D ⌈/⌉ p) :=
      (ceilDiv_le_iff_le_mul hp0).1 le_rfl
    have hpowCeil : p ^ (n + 2) ≤ D ⌈/⌉ p := by
      by_contra h
      have hlt : D ⌈/⌉ p < p ^ (n + 2) := Nat.lt_of_not_ge h
      have hmul : p * (D ⌈/⌉ p) < p * p ^ (n + 2) :=
        (Nat.mul_lt_mul_left hp0).2 hlt
      have hpowsucc : p * p ^ (n + 2) = p ^ (n + 3) := by
        calc
          p * p ^ (n + 2) = p ^ (n + 2) * p := Nat.mul_comm _ _
          _ = p ^ ((n + 2) + 1) := (pow_succ _ _).symm
          _ = p ^ (n + 3) := by congr 1 <;> omega
      rw [hpowsucc] at hmul
      omega
    rw [suzukiSourceV_eq_zero_of_pow_le_allDepth S n (D ⌈/⌉ p) p hpowCeil, mul_zero]

/-- Case I's exact discrete recurrence.  The hypothesis is needed only in odd
parity; for even `N` it is vacuous.  The assumptions `2 ≤ N` and the natural
ceiling quotient are explicit. -/
theorem suzukiActualT_caseI_recurrence
    (S : BoundingSieve) {N D z : ℕ} (hN : 2 ≤ N)
    (hOddBoundary : Odd N → z ^ 3 ≤ D) :
    suzukiActualT S N D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p := by
  induction N using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more n ih ih1 =>
      cases n with
      | zero =>
          have hv := suzukiSourceV_succ_eq_unrestricted
            (S := S) (n := 1) (D := D) (z := z) (by omega)
            (by simp)
          simpa [suzukiActualT] using hv
      | succ n =>
          cases n with
          | zero =>
              have hz3 : z ^ 3 ≤ D := hOddBoundary (by norm_num)
              have hv1 := suzukiSourceV_eq_zero_of_pow_le_allDepth S 1 D z (by simpa using hz3)
              have hv3 := suzukiSourceV_succ_eq_unrestricted
                (S := S) (n := 2) (D := D) (z := z) (by omega)
                (by intro _; exact hz3)
              simpa [suzukiActualT, hv1] using hv3
          | succ k =>
              have hOddSmall : Odd (k + 2) → z ^ 3 ≤ D := by
                intro hk
                apply hOddBoundary
                have hk' : Odd ((k + 2) + 2) :=
                  hk.add_even (by norm_num : Even (2 : ℕ))
                convert hk' using 1 <;> omega
              have hrecSmall := ih (by omega : 2 ≤ k + 2) hOddSmall
              have hv := suzukiSourceV_succ_eq_unrestricted
                (S := S) (n := k + 3) (D := D) (z := z) (by omega)
                (by
                  intro hk
                  apply hOddBoundary
                  convert hk using 1 <;> omega)
              rw [suzukiActualT_add_two, hv, hrecSmall]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro p hp
              change S.nu p * suzukiSourceV S (k + 3) (D ⌈/⌉ p) p +
                  S.nu p * suzukiActualT S (k + 1) (D ⌈/⌉ p) p =
                S.nu p * suzukiActualT S (k + 3) (D ⌈/⌉ p) p
              rw [show k + 3 = (k + 1) + 2 by omega, suzukiActualT_add_two]
              ring

/-- The three finite pieces in Suzuki (14.9).  The support already contains
`p < z`; `a` and `b` are respectively `D^(1/σ)` and `D^(1/τ)`. -/
noncomputable def suzukiSigmaZero
    (S : BoundingSieve) (N D z : ℕ) (a : ℝ) : ℝ :=
  ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p : ℕ => (p : ℝ) < a),
    S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p

noncomputable def suzukiSigmaOne
    (S : BoundingSieve) (N D z : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ (suzukiSupportedBelow S z).filter
      (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b),
    S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p

noncomputable def suzukiSigmaTwo
    (S : BoundingSieve) (N D z : ℕ) (b : ℝ) : ℝ :=
  ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p : ℕ => b ≤ (p : ℝ)),
    S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p

/-- Equation (14.9), before substituting the two real-power endpoints.  This is
an equality of finite sums, including all boundary choices (`<`, `≤`) exactly. -/
theorem suzuki_equation14_9
    (S : BoundingSieve) {N D z : ℕ} (hN : 2 ≤ N)
    (hOddBoundary : Odd N → z ^ 3 ≤ D) {a b : ℝ} (hab : a ≤ b) :
    suzukiActualT S N D z =
      suzukiSigmaZero S N D z a + suzukiSigmaOne S N D z a b +
        suzukiSigmaTwo S N D z b := by
  rw [suzukiActualT_caseI_recurrence S hN hOddBoundary]
  unfold suzukiSigmaZero suzukiSigmaOne suzukiSigmaTwo
  let P := suzukiSupportedBelow S z
  let f : ℕ → ℝ := fun p => S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p
  change (∑ p ∈ P, f p) =
    (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < a), f p) +
      (∑ p ∈ P.filter (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b), f p) +
        ∑ p ∈ P.filter (fun p : ℕ => b ≤ (p : ℝ)), f p
  calc
    (∑ p ∈ P, f p) =
        (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < a), f p) +
          ∑ p ∈ P.filter (fun p : ℕ => ¬ (p : ℝ) < a), f p :=
      (Finset.sum_filter_add_sum_filter_not P
        (fun p : ℕ => (p : ℝ) < a) f).symm
    _ = (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < a), f p) +
          ((∑ p ∈ P.filter (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b), f p) +
            ∑ p ∈ P.filter (fun p : ℕ => b ≤ (p : ℝ)), f p) := by
      congr 1
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (P.filter (fun p : ℕ => ¬ (p : ℝ) < a))
        (fun p : ℕ => (p : ℝ) < b) f
      rw [← hsplit]
      congr 1
      · apply Finset.sum_congr
          (by ext p; simp [not_lt, and_assoc])
        intro p hp
        rfl
      · apply Finset.sum_congr
          (by
            ext p
            simp only [Finset.mem_filter, not_lt]
            constructor
            · rintro ⟨⟨hpP, hap⟩, hbp⟩
              exact ⟨hpP, hbp⟩
            · rintro ⟨hpP, hbp⟩
              exact ⟨⟨hpP, hab.trans hbp⟩, hbp⟩)
        intro p hp
        rfl
    _ = (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < a), f p) +
          (∑ p ∈ P.filter (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b), f p) +
            ∑ p ∈ P.filter (fun p : ℕ => b ≤ (p : ℝ)), f p := by ring


end MathlibNt.SieveTheory
