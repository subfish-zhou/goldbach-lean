import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier

/-!
# Suzuki (14.9) with the strict natural-ceiling carrier

The odd-depth recurrence needs only the source condition `p^3 < D` for the
actual summation indices `p < z`.  It does not need the generally false
natural-ceiling surrogate `z^3 ≤ D`.
-/

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

/-- The depth-one source layer vanishes when every natural below the strict
cutoff satisfies the cubic source bound. -/
theorem suzukiSourceV_one_eq_zero_of_cube_lt_below
    (S : BoundingSieve) {D z : ℕ}
    (hCube : ∀ p < z, p ^ 3 < D) :
    suzukiSourceV S 1 D z = 0 := by
  rw [suzukiSourceV_one]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter] at hp
  rcases hp with ⟨hpSupport, hDp⟩
  have hpz : p < z := (Finset.mem_filter.mp hpSupport).2
  exact (not_lt_of_ge hDp (hCube p hpz)).elim

/-- The exact successor recurrence after erasing the lower source cutoff.
At odd depth its upper cutoff is automatic from the strict carrier condition
on the indices actually present in the sum. -/
theorem suzukiSourceV_succ_eq_unrestricted_strict
    (S : BoundingSieve) {n D z : ℕ} (hn : 0 < n)
    (hOddCarrier : Odd (n + 1) → ∀ p < z, p ^ 3 < D) :
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
    have hp0 : 0 < p := hpPrime.pos
    have hUpper : Odd (n + 1) → p ^ 3 < D := by
      intro hodd
      exact hOddCarrier hodd p hpz
    have hLowerFails : ¬ D ≤ p ^ ((n + 1) + 2) := by
      intro hLower
      apply hpNotCarrier
      simp only [suzukiSourceOuterCarrier, Finset.mem_filter]
      exact ⟨⟨hpSupport'.1, hpz⟩, hLower, hUpper⟩
    have hpowD : p ^ (n + 3) < D := by
      have h := Nat.lt_of_not_ge hLowerFails
      convert h using 1
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
          _ = p ^ (n + 3) := by congr 1
      rw [hpowsucc] at hmul
      omega
    rw [suzukiSourceV_eq_zero_of_pow_le_allDepth S n (D ⌈/⌉ p) p hpowCeil, mul_zero]

/-- Case I's actual finite recurrence under the source-faithful odd condition.
The strict inequality is required only for indices `p < z`. -/
theorem suzukiActualT_caseI_recurrence_strict
    (S : BoundingSieve) {N D z : ℕ} (hN : 2 ≤ N)
    (hOddCarrier : Odd N → ∀ p < z, p ^ 3 < D) :
    suzukiActualT S N D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p := by
  induction N using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more n ih ih1 =>
      cases n with
      | zero =>
          have hv := suzukiSourceV_succ_eq_unrestricted_strict
            (S := S) (n := 1) (D := D) (z := z) (by omega)
            (by simp)
          simpa [suzukiActualT] using hv
      | succ n =>
          cases n with
          | zero =>
              have hCube : ∀ p < z, p ^ 3 < D :=
                hOddCarrier (by norm_num)
              have hv1 := suzukiSourceV_one_eq_zero_of_cube_lt_below S hCube
              have hv3 := suzukiSourceV_succ_eq_unrestricted_strict
                (S := S) (n := 2) (D := D) (z := z) (by omega)
                (by intro _; exact hCube)
              simpa [suzukiActualT, hv1] using hv3
          | succ k =>
              have hOddSmall : Odd (k + 2) → ∀ p < z, p ^ 3 < D := by
                intro hk
                apply hOddCarrier
                have hk' : Odd ((k + 2) + 2) :=
                  hk.add_even (by norm_num : Even (2 : ℕ))
                convert hk' using 1
              have hrecSmall := ih (by omega : 2 ≤ k + 2) hOddSmall
              have hv := suzukiSourceV_succ_eq_unrestricted_strict
                (S := S) (n := k + 3) (D := D) (z := z) (by omega)
                (by
                  intro hk
                  apply hOddCarrier
                  convert hk using 1)
              rw [suzukiActualT_add_two, hv, hrecSmall]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro p hp
              change S.nu p * suzukiSourceV S (k + 3) (D ⌈/⌉ p) p +
                  S.nu p * suzukiActualT S (k + 1) (D ⌈/⌉ p) p =
                S.nu p * suzukiActualT S (k + 3) (D ⌈/⌉ p) p
              rw [show k + 3 = (k + 1) + 2 by omega, suzukiActualT_add_two]
              ring

/-- Equation (14.9) with the exact strict odd carrier hypothesis. -/
theorem suzuki_equation14_9_strict
    (S : BoundingSieve) {N D z : ℕ} (hN : 2 ≤ N)
    (hOddCarrier : Odd N → ∀ p < z, p ^ 3 < D)
    {a b : ℝ} (hab : a ≤ b) :
    suzukiActualT S N D z =
      suzukiSigmaZero S N D z a + suzukiSigmaOne S N D z a b +
        suzukiSigmaTwo S N D z b := by
  rw [suzukiActualT_caseI_recurrence_strict S hN hOddCarrier]
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

/-- A natural ceiling of `D^(1/s)` with `s ≥ 3` supplies exactly the strict
cubic carrier needed by the odd recurrence. -/
theorem cube_lt_of_lt_natCeil_rpow
    {D z p : ℕ} {s : ℝ} (hD : 0 < D) (hs : 3 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) (hpz : p < z) :
    p ^ 3 < D := by
  have hs0 : 0 < s := by linarith
  have hx0 : 0 < (D : ℝ) ^ (1 / s) := natCast_rpow_one_div_pos hD s
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / s) :=
    (nat_lt_natCeil_iff_lt_real hx0 hz).1 hpz
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hroot_le : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 / (3 : ℝ)) :=
    rpow_one_div_mono_of_le hD1 (by norm_num) hs
  have hpCubeRoot : (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) :=
    hpRoot.trans_le hroot_le
  have hr := Real.lt_rpow_inv_iff_of_pos
    (x := (p : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  norm_num [one_div] at hr
  have hcubeR : (p : ℝ) ^ (3 : ℕ) < (D : ℝ) := hr.mp hpCubeRoot
  exact_mod_cast hcubeR

/-- Natural-ceiling specialization of the actual recurrence. -/
theorem suzukiActualT_caseI_recurrence_natCeil
    (S : BoundingSieve) {N D z : ℕ} {s : ℝ} (hN : 2 ≤ N)
    (hD : 0 < D) (hs : 3 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p := by
  apply suzukiActualT_caseI_recurrence_strict S hN
  intro _ p hpz
  exact cube_lt_of_lt_natCeil_rpow hD hs hz hpz

/-- Natural-ceiling specialization of Suzuki's decomposition (14.9). -/
theorem suzuki_equation14_9_natCeil
    (S : BoundingSieve) {N D z : ℕ} {s : ℝ} (hN : 2 ≤ N)
    (hD : 0 < D) (hs : 3 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    {a b : ℝ} (hab : a ≤ b) :
    suzukiActualT S N D z =
      suzukiSigmaZero S N D z a + suzukiSigmaOne S N D z a b +
        suzukiSigmaTwo S N D z b := by
  apply suzuki_equation14_9_strict S hN _ hab
  intro _ p hpz
  exact cube_lt_of_lt_natCeil_rpow hD hs hz hpz


end MathlibNt.SieveTheory
