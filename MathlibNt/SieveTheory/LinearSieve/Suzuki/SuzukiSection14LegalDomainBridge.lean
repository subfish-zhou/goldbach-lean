import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVnSemanticResolution

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- General upper support of the source-faithful layer. -/
theorem suzukiSourceV_eq_zero_of_pow_le
    (S : BoundingSieve) {n D z : ℕ} (hn : 1 ≤ n) (hzD : z ^ (n + 2) ≤ D) :
    suzukiSourceV S n D z = 0 := by
  classical
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          rw [suzukiSourceV_one]
          norm_num at hzD
          apply sum_eq_zero
          intro p hp
          have hmem := mem_filter.mp hp
          have hpz : p < z := (mem_filter.mp hmem.1).2
          have hp3z3 : p ^ 3 < z ^ 3 := Nat.pow_lt_pow_left hpz (by norm_num)
          omega
      | succ n =>
          rw [suzukiSourceV_succ_of_pos S (by omega)]
          apply sum_eq_zero
          intro p hp
          have hcarrier := mem_filter.mp hp
          have hpz : p < z := (mem_filter.mp hcarrier.1).2
          have hDpow : D ≤ p ^ (n + 4) := by
            simpa [Nat.add_assoc] using hcarrier.2.1
          have hzD' : z ^ (n + 4) ≤ D := by
            simpa [Nat.add_assoc] using hzD
          have hpPow : p ^ (n + 4) < z ^ (n + 4) :=
            Nat.pow_lt_pow_left hpz (by omega)
          omega

/-- If the Lemma 7.1 lower outer cutoff fails, the recursively remaining
layer vanishes. -/
theorem suzukiSourceV_inner_eq_zero_of_outer_lower_fails
    (S : BoundingSieve) {n D p : ℕ} (hn : 1 ≤ n) (hp : 0 < p)
    (hfail : ¬ D ≤ p ^ (n + 3)) :
    suzukiSourceV S n (D ⌈/⌉ p) p = 0 := by
  apply suzukiSourceV_eq_zero_of_pow_le S hn
  by_contra h
  have hceil : D ⌈/⌉ p ≤ p ^ (n + 2) := Nat.le_of_not_ge h
  have hDmul : D ≤ p * p ^ (n + 2) :=
    (ceilDiv_le_iff_le_mul hp).1 hceil
  have hpow : p * p ^ (n + 2) = p ^ (n + 3) := by ring
  apply hfail
  simpa [hpow] using hDmul


end MathlibNt.SieveTheory
