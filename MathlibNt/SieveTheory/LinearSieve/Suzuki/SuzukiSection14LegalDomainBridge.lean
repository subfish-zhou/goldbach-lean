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

/-- Legal-domain recurrence: the source carrier may be extended to every
supported `p < z`.  The odd-index upper cutoff is automatic from `z^3 ≤ D`;
the omitted lower-cutoff terms vanish by the preceding support lemma. -/
theorem suzukiSourceV_eq_extended_recurrence
    (S : BoundingSieve) {n D z : ℕ} (hn : 2 ≤ n)
    (hoddDomain : Odd n → z ^ 3 ≤ D) :
    suzukiSourceV S n D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiSourceV S (n - 1) (D ⌈/⌉ p) p := by
  classical
  have hpred : 0 < n - 1 := by omega
  have hnrepr : n - 1 + 1 = n := by omega
  rw [← hnrepr, suzukiSourceV_succ_of_pos S hpred]
  apply sum_subset
  · intro p hp
    exact (mem_filter.mp hp).1
  · intro p hpfull hpsource
    have hpP : p ∈ S.prodPrimes.primeFactors := (mem_filter.mp hpfull).1
    have hpz : p < z := (mem_filter.mp hpfull).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hp0 : 0 < p := hpprime.pos
    have hnotPred : ¬ (D ≤ p ^ ((n - 1 + 1) + 2) ∧
        (Odd (n - 1 + 1) → p ^ 3 < D)) := by
      intro hpreds
      apply hpsource
      exact mem_filter.mpr ⟨hpfull, hpreds⟩
    have hlowerFail : ¬ D ≤ p ^ (n + 2) := by
      intro hlower
      apply hnotPred
      refine ⟨?_, ?_⟩
      · simpa [hnrepr] using hlower
      · intro hnodd
        have hz3D := hoddDomain (by simpa [hnrepr] using hnodd)
        have hp3z3 : p ^ 3 < z ^ 3 := Nat.pow_lt_pow_left hpz (by norm_num)
        omega
    have hzero : suzukiSourceV S (n - 1) (D ⌈/⌉ p) p = 0 := by
      apply suzukiSourceV_inner_eq_zero_of_outer_lower_fails S (by omega) hp0
      simpa [show n - 1 + 3 = n + 2 by omega] using hlowerFail
    rw [hzero, mul_zero]

/-- Index two: no parity-domain hypothesis is needed. -/
theorem suzukiSourceV_two_eq_extended_recurrence
    (S : BoundingSieve) (D z : ℕ) :
    suzukiSourceV S 2 D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiSourceV S 1 (D ⌈/⌉ p) p := by
  simpa using suzukiSourceV_eq_extended_recurrence S (n := 2) (D := D) (z := z)
    (by norm_num) (by norm_num)

/-- Index three: `z^3 ≤ D` is exactly the legal odd-domain assumption making
Suzuki's extra outer upper cutoff automatic. -/
theorem suzukiSourceV_three_eq_extended_recurrence
    (S : BoundingSieve) {D z : ℕ} (hzD : z ^ 3 ≤ D) :
    suzukiSourceV S 3 D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiSourceV S 2 (D ⌈/⌉ p) p := by
  simpa using suzukiSourceV_eq_extended_recurrence S (n := 3) (D := D) (z := z)
    (by norm_num) (fun _ => hzD)

/-- Exact induction invariant for the full bridge: at layer `n`, `z^n ≤ D`
propagates to `p^(n-1) ≤ ceil(D/p)` for every supported outer prime `p < z`.
This simultaneously makes every odd source upper cutoff automatic. -/
theorem suzukiSourceV_eq_section14ExtendedV_of_pow_le
    (S : BoundingSieve) (n D z : ℕ) (hzD : z ^ n ≤ D) :
    suzukiSourceV S n D z = section14ExtendedV S n D z := by
  induction n using Nat.strong_induction_on generalizing D z with
  | h n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero =>
              have hzD' : z ≤ D := by simpa using hzD
              rw [suzukiSourceV_one, section14ExtendedV_one]
              apply sum_congr
              · ext p
                simp only [mem_filter]
                constructor
                · rintro ⟨hp, hpD⟩
                  exact ⟨hp, (mem_filter.mp hp).2.trans_le hzD', hpD⟩
                · rintro ⟨hp, _, hpD⟩
                  exact ⟨hp, hpD⟩
              · intro p hp
                rfl
          | succ k =>
              by_cases hz : z = 0
              · subst z
                rw [suzukiSourceV_eq_extended_recurrence S (by omega)]
                · simp [section14ExtendedV, suzukiSupportedBelow]
                · intro _
                  simp
              · have hzpos : 0 < z := Nat.pos_of_ne_zero hz
                have hoddDomain : Odd (k + 2) → z ^ 3 ≤ D := by
                  intro hodd
                  have hk3 : 3 ≤ k + 2 := by
                    rcases hodd with ⟨j, hj⟩
                    omega
                  exact (Nat.pow_le_pow_right hzpos hk3).trans hzD
                rw [suzukiSourceV_eq_extended_recurrence S (by omega) hoddDomain]
                unfold section14ExtendedV
                apply sum_congr rfl
                intro p hp
                congr 1
                apply ih (k + 1) (by omega)
                have hpP : p ∈ S.prodPrimes.primeFactors := (mem_filter.mp hp).1
                have hpz : p < z := (mem_filter.mp hp).2
                have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
                have hp0 : 0 < p := hpprime.pos
                by_contra hnot
                have hceil : D ⌈/⌉ p ≤ p ^ (k + 1) := Nat.le_of_not_ge hnot
                have hDmul : D ≤ p * p ^ (k + 1) :=
                  (ceilDiv_le_iff_le_mul hp0).1 hceil
                have hpow : p * p ^ (k + 1) = p ^ (k + 2) := by ring
                have hpPow : p ^ (k + 2) < z ^ (k + 2) :=
                  Nat.pow_lt_pow_left hpz (by omega)
                rw [hpow] at hDmul
                have hzD' : z ^ (k + 2) ≤ D := by
                  simpa [Nat.add_assoc] using hzD
                exact (not_lt_of_ge hDmul) (hpPow.trans_le hzD')

/-- Index two closes under the exact even legal-domain hypothesis. -/
theorem suzukiSourceV_two_eq_section14ExtendedV
    (S : BoundingSieve) {D z : ℕ} (hzD : z ^ 2 ≤ D) :
    suzukiSourceV S 2 D z = section14ExtendedV S 2 D z :=
  suzukiSourceV_eq_section14ExtendedV_of_pow_le S 2 D z hzD

/-- Index three closes under the exact odd legal-domain hypothesis. -/
theorem suzukiSourceV_three_eq_section14ExtendedV
    (S : BoundingSieve) {D z : ℕ} (hzD : z ^ 3 ≤ D) :
    suzukiSourceV S 3 D z = section14ExtendedV S 3 D z :=
  suzukiSourceV_eq_section14ExtendedV_of_pow_le S 3 D z hzD

/-- Consequently the source-faithful parity sum agrees with the renamed §14
extended sum on the uniform legal domain `z^N ≤ D`. -/
theorem suzukiSourceParitySum_eq_section14ExtendedT_of_pow_le
    (S : BoundingSieve) (N D z : ℕ) (hzD : z ^ N ≤ D) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      section14ExtendedT S N D z := by
  classical
  unfold section14ExtendedT
  apply Finset.sum_congr rfl
  intro n hn
  apply suzukiSourceV_eq_section14ExtendedV_of_pow_le
  have hnBounds : 1 ≤ n ∧ n ≤ N := by
    have hmem := (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mp hmem
  by_cases hz : z = 0
  · subst z
    simp [Nat.ne_of_gt hnBounds.1]
  · exact (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hz) hnBounds.2).trans hzD


end MathlibNt.SieveTheory
