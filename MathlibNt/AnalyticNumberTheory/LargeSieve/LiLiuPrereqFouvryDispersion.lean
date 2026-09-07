import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The finite signed dispersion reduction

The arithmetic sums below are the finite-support versions of Fouvry (1987),
(3.4), and Fouvry (1984), (7.7)--(7.10). No absolute values are inserted
inside the modulus sum. The integer residue and the two supports are arbitrary.

The square expansion and Cauchy--Schwarz reduction are proved here; no
logarithmic saving, Siegel--Walfisz estimate or Kloosterman estimate is assumed.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

def progressionMass (N : Finset ℕ) (β : ℕ → ℝ) (a : ℤ) (q m : ℕ) : ℝ :=
  ∑ n ∈ N, if Int.ModEq q ((m : ℤ) * n) a then β n else 0

def coprimeMass (N : Finset ℕ) (β : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ n ∈ N, if n.Coprime q then β n else 0

def bilinearDiscrepancy (M N : Finset ℕ) (α β : ℕ → ℝ) (a : ℤ) (q : ℕ) : ℝ :=
  (∑ m ∈ M, ∑ n ∈ N,
      if Int.ModEq q ((m : ℤ) * n) a then α m * β n else 0) -
    (∑ m ∈ M, ∑ n ∈ N, if (m * n).Coprime q then α m * β n else 0) /
      (q.totient : ℝ)

def reducedModuli (Q : Finset ℕ) (a : ℤ) : Finset ℕ :=
  Q.filter (fun q => Int.gcd a q = 1)

def signedError (M N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, c q * bilinearDiscrepancy M N α β a q

def progressionRow (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) (m : ℕ) : ℝ :=
  ∑ q ∈ reducedModuli Q a,
    if m.Coprime q then c q * progressionMass N β a q m else 0

def principalRow (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) (m : ℕ) : ℝ :=
  ∑ q ∈ reducedModuli Q a,
    if m.Coprime q then c q * coprimeMass N β q / (q.totient : ℝ) else 0

theorem coprime_of_product_congruent {a : ℤ} {q m n : ℕ}
    (ha : Int.gcd a q = 1) (h : Int.ModEq q ((m : ℤ) * n) a) :
    m.Coprime q ∧ n.Coprime q := by
  have hg : Int.gcd ((m : ℤ) * n) q = 1 := by
    rw [← Int.gcd_emod ((m : ℤ) * n) q, h.eq, Int.gcd_emod, ha]
  have hmn : (m * n).Coprime q := by
    simpa [Int.gcd, Int.natAbs_mul] using hg
  exact Nat.coprime_mul_iff_left.mp hmn

theorem progressionMass_eq_zero_of_not_coprime
    (N : Finset ℕ) (β : ℕ → ℝ) {a : ℤ} {q m : ℕ}
    (ha : Int.gcd a q = 1) (hm : ¬m.Coprime q) :
    progressionMass N β a q m = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  exact if_neg (fun h => hm (coprime_of_product_congruent ha h).1)

theorem sum_coprime_product_factor (N : Finset ℕ) (α β : ℕ → ℝ) (m q : ℕ) :
    (∑ n ∈ N, if (m * n).Coprime q then α m * β n else 0) =
      if m.Coprime q then α m * coprimeMass N β q else 0 := by
  by_cases hm : m.Coprime q
  · simp only [Nat.coprime_mul_iff_left, Nat.Coprime, hm, true_and, ite_true,
      coprimeMass, Finset.mul_sum, mul_ite, mul_zero]
  · simp [Nat.coprime_mul_iff_left, hm]

theorem bilinearDiscrepancy_eq_rows
    (M N : Finset ℕ) (α β : ℕ → ℝ) {a : ℤ} {q : ℕ}
    (ha : Int.gcd a q = 1) :
    bilinearDiscrepancy M N α β a q =
      ∑ m ∈ M, α m * (if m.Coprime q then
        progressionMass N β a q m - coprimeMass N β q / (q.totient : ℝ)
        else 0) := by
  have hp (m : ℕ) :
      (∑ n ∈ N, if Int.ModEq q ((m : ℤ) * n) a then α m * β n else 0) =
        α m * progressionMass N β a q m := by
    simp [progressionMass, Finset.mul_sum, mul_ite]
  simp_rw [bilinearDiscrepancy, hp, sum_coprime_product_factor]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.Coprime q
  · simp only [if_pos hm]
    ring
  · simp [hm, progressionMass_eq_zero_of_not_coprime N β ha hm]

theorem signedError_eq_rows
    (M N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) :
    signedError M N Q α β c a =
      ∑ m ∈ M, α m * (progressionRow N Q β c a m - principalRow N Q β c a m) := by
  calc
    _ = ∑ q ∈ reducedModuli Q a, ∑ m ∈ M, α m *
        (if m.Coprime q then c q *
          (progressionMass N β a q m - coprimeMass N β q / (q.totient : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [bilinearDiscrepancy_eq_rows M N α β (Finset.mem_filter.mp hq).2,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m.Coprime q
      · simp only [if_pos hm]
        ring
      · simp only [if_neg hm, mul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      unfold progressionRow principalRow
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hm : m.Coprime q
      · simp only [if_pos hm]
        ring
      · simp only [if_neg hm, sub_self]

def dispersionW (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ m ∈ S, w m * progressionRow N Q β c a m ^ 2

def dispersionV (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ m ∈ S, w m * progressionRow N Q β c a m * principalRow N Q β c a m

def dispersionU (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ m ∈ S, w m * principalRow N Q β c a m ^ 2

theorem dispersion_identity
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) :
    (∑ m ∈ S, w m * (progressionRow N Q β c a m - principalRow N Q β c a m) ^ 2) =
      dispersionW S N Q w β c a - 2 * dispersionV S N Q w β c a +
        dispersionU S N Q w β c a := by
  unfold dispersionW dispersionV dispersionU
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem dispersion_nonneg
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ)
    (hw : ∀ m ∈ S, 0 ≤ w m) :
    0 ≤ dispersionW S N Q w β c a - 2 * dispersionV S N Q w β c a +
      dispersionU S N Q w β c a := by
  rw [← dispersion_identity]
  exact Finset.sum_nonneg (fun m hm => mul_nonneg (hw m hm) (sq_nonneg _))

theorem signedError_sq_le_dispersion
    (M N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) :
    signedError M N Q α β c a ^ 2 ≤
      (∑ m ∈ M, α m ^ 2) *
        (dispersionW M N Q (fun _ => 1) β c a -
          2 * dispersionV M N Q (fun _ => 1) β c a +
          dispersionU M N Q (fun _ => 1) β c a) := by
  rw [signedError_eq_rows, ← dispersion_identity]
  simpa only [one_mul] using Finset.sum_mul_sq_le_sq_mul_sq M α
    (fun m => progressionRow N Q β c a m - principalRow N Q β c a m)

/-- A nonnegative cutoff majorizing 1 on the alpha support may enlarge the m-sum. -/
theorem signedError_sq_le_smoothed_dispersion
    (M S N Q : Finset ℕ) (α β c w : ℕ → ℝ) (a : ℤ)
    (hMS : M ⊆ S) (hw : ∀ m ∈ S, 0 ≤ w m) (hmajor : ∀ m ∈ M, 1 ≤ w m) :
    signedError M N Q α β c a ^ 2 ≤
      (∑ m ∈ M, α m ^ 2) *
        (dispersionW S N Q w β c a - 2 * dispersionV S N Q w β c a +
          dispersionU S N Q w β c a) := by
  apply (signedError_sq_le_dispersion M N Q α β c a).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [← dispersion_identity, ← dispersion_identity]
  apply (Finset.sum_le_sum (s := M) (fun m hm =>
    mul_le_mul_of_nonneg_right (hmajor m hm) (sq_nonneg _))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hMS
    (fun m hm _ => mul_nonneg (hw m hm) (sq_nonneg _))

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
