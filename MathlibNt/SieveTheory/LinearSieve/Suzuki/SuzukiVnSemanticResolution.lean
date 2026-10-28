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


end MathlibNt.SieveTheory
