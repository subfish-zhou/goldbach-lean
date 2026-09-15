/-
Source-faithful repair of the total discrete Suzuki V_n API (beta = 2).

Suzuki (6.2) defines V_n by complete decreasing prime chains.  Lemma 7.1 does
not give the unbounded recursion used by `section14ExtendedV`: its outer prime is
restricted by y_n <= p < z_n.  For beta = 2 those restrictions are represented
integrally by

  D <= p^(n+2), and, when n is odd, p^3 < D,

in addition to p < z.  The source later removes the lower cutoff only after a
support-vanishing argument, and only in the parity domain used in Section 14.
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDiscreteParityRecurrence

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- Exact integral outer carrier in Suzuki Lemma 7.1 for beta = 2.

`n` is the complete source index.  `D <= p^(n+2)` is `y_n <= p`; for odd `n`,
`p^3 < D` is the extra upper cutoff in `z_n = min(z,D^(1/3))`. -/
def suzukiSourceOuterCarrier (n D z : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (P.filter (fun p => p < z)).filter fun p =>
    D ≤ p ^ (n + 2) ∧ (Odd n → p ^ 3 < D)

/-- A total, source-faithful beta=2 recursion.  Unlike the old
`section14ExtendedV`, the base does not invent `p < D`, and every successor keeps
Suzuki's `y_n` and (odd-index) `z_n` cutoffs. -/
noncomputable def suzukiSourceV (S : BoundingSieve) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | 1, D, z =>
      ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => D ≤ p ^ 3),
        S.nu p * sourceDiscreteEuler S p
  | n + 2, D, z =>
      ∑ p ∈ suzukiSourceOuterCarrier (n + 2) D z S.prodPrimes.primeFactors,
        S.nu p * suzukiSourceV S (n + 1) (D ⌈/⌉ p) p

@[simp] theorem suzukiSourceV_one (S : BoundingSieve) (D z : ℕ) :
    suzukiSourceV S 1 D z =
      ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => D ≤ p ^ 3),
        S.nu p * sourceDiscreteEuler S p := rfl

/-- Correct total recurrence: the outer source carrier cannot be erased
without the Section 14 domain/support hypotheses. -/
theorem suzukiSourceV_succ_of_pos
    (S : BoundingSieve) {n : ℕ} (hn : 0 < n) (D z : ℕ) :
    suzukiSourceV S (n + 1) D z =
      ∑ p ∈ suzukiSourceOuterCarrier (n + 1) D z S.prodPrimes.primeFactors,
        S.nu p * suzukiSourceV S n (D ⌈/⌉ p) p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rfl

/-- The corrected index-two carrier before simplification.  It has no invented
`q < ceil(D/p)` condition. -/
theorem suzukiSourceV_two_eq (S : BoundingSieve) (D z : ℕ) :
    suzukiSourceV S 2 D z =
      ∑ p ∈ suzukiSourceOuterCarrier 2 D z S.prodPrimes.primeFactors,
        S.nu p *
          ∑ q ∈ (suzukiSupportedBelow S p).filter
              (fun q => D ⌈/⌉ p ≤ q ^ 3),
            S.nu q * sourceDiscreteEuler S q := by
  rfl

/-- At n=2 Suzuki's literal terminal test accepts (D,p,q)=(9,5,2), while the
Section 14 extended recursive totalization rejects it because it additionally asks q<D/p. -/
theorem section14Extended_n2_rejects_source_chain :
    (9 ≤ 5 * 2 ^ 3) ∧
      ¬ (2 < 9 ⌈/⌉ 5 ∧ 9 ⌈/⌉ 5 ≤ 2 ^ 3) := by
  norm_num

/-- The production lower-boundary singleton accepts the same source chain:
its active-prefix clause is `p<D`, not the Section 14 extended recursive `p*q<D`. -/
theorem lower_boundary_n2_accepts_source_chain :
    (5 < 9 ∧ 9 ≤ 5 * 2 ^ 3) := by
  norm_num

/-- In Suzuki's even parity domain (`z^2 <= D`), the lower boundary's apparent
extra n=2 prefix `p<D` is automatic. -/
theorem lower_boundary_n2_prefix_redundant
    {D z p : ℕ} (hp2 : 2 ≤ p) (hpz : p < z) (hzD : z ^ 2 ≤ D) : p < D := by
  have hp2lt : p < p ^ 2 := by nlinarith
  have hpow : p ^ 2 < z ^ 2 := Nat.pow_lt_pow_left hpz (by norm_num)
  omega

/-- In the same domain, the old divided-level predicate and Suzuki's literal
n=2 terminal condition agree.  Thus the mismatch is outside the theorem's
legal domain, not a missing lower-chain prefix. -/
theorem section14Extended_n2_iff_source_in_even_domain
    {D z p q : ℕ} (hp : 0 < p) (hq : q < p) (hpz : p < z)
    (hzD : z ^ 2 ≤ D) :
    (q < D ⌈/⌉ p ∧ D ⌈/⌉ p ≤ q ^ 3) ↔ D ≤ p * q ^ 3 := by
  have hpqD : p * q < D := by
    have hp2z2 : p ^ 2 < z ^ 2 := Nat.pow_lt_pow_left hpz (by norm_num)
    have hpq_lt_p2 : p * q < p ^ 2 := by
      simpa [pow_two] using (Nat.mul_lt_mul_left hp).2 hq
    omega
  have hqceil : q < D ⌈/⌉ p := by
    rw [← not_le, ceilDiv_le_iff_le_mul hp]
    omega
  constructor
  · rintro ⟨_, hceil⟩
    exact (ceilDiv_le_iff_le_mul hp).1 hceil
  · intro hterminal
    exact ⟨hqceil, (ceilDiv_le_iff_le_mul hp).2 hterminal⟩


end MathlibNt.SieveTheory
