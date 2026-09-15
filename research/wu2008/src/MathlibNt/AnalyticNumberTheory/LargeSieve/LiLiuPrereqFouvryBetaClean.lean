import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise

/-!
# Removing the divisors of a changing nonzero residue from beta

The deleted mass is bounded by one divisor sum, including at order zero.
The subpolynomial constant precedes the residue, scale, support and sequence.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

def betaClean (β : ℕ → ℝ) (a : ℤ) (n : ℕ) : ℝ :=
  if (n : ℤ) ∣ a then 0 else β n

def betaDivisorPart (β : ℕ → ℝ) (a : ℤ) (n : ℕ) : ℝ :=
  if (n : ℤ) ∣ a then β n else 0

theorem beta_eq_clean_add_divisorPart (β : ℕ → ℝ) (a : ℤ) (n : ℕ) :
    β n = betaClean β a n + betaDivisorPart β a n := by
  unfold betaClean betaDivisorPart
  split_ifs <;> simp

theorem abs_betaClean_le (β : ℕ → ℝ) (a : ℤ) (n : ℕ) :
    |betaClean β a n| ≤ |β n| := by
  unfold betaClean
  split_ifs <;> simp

theorem abs_betaDivisorPart_le (β : ℕ → ℝ) (a : ℤ) (n : ℕ) :
    |betaDivisorPart β a n| ≤ |β n| := by
  unfold betaDivisorPart
  split_ifs <;> simp

theorem betaClean_nonzero_not_dvd {β : ℕ → ℝ} {a : ℤ} {n : ℕ}
    (hn : betaClean β a n ≠ 0) : ¬(n : ℤ) ∣ a := by
  intro hd
  exact hn (if_pos hd)

theorem support_betaClean_subset (β : ℕ → ℝ) (a : ℤ) :
    Function.support (betaClean β a) ⊆ Function.support β := by
  intro n hn
  change β n ≠ 0
  intro h
  exact hn (by simp [betaClean, h])

theorem support_betaDivisorPart_subset (β : ℕ → ℝ) (a : ℤ) :
    Function.support (betaDivisorPart β a) ⊆ Function.support β := by
  intro n hn
  change β n ≠ 0
  intro h
  exact hn (by simp [betaDivisorPart, h])

theorem betaClean_abs_le_fouvryTau {k : ℕ} {N : Finset ℕ}
    {β : ℕ → ℝ} (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) (a : ℤ) :
    ∀ n ∈ N, |betaClean β a n| ≤ (fouvryTau k n : ℝ) :=
  fun n hn => (abs_betaClean_le β a n).trans (hβ n hn)

/-- The summand indexed by `n` proves monotonicity even when the lower order
is zero; at `n = 0` both sides vanish. -/
theorem fouvryTau_le_succ (k n : ℕ) :
    fouvryTau k n ≤ fouvryTau (k + 1) n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [fouvryTau_succ]
  exact single_le_sum (fun d _ => Nat.zero_le (fouvryTau k d))
    (Nat.mem_divisors_self n hn)

/-- No positivity or interval-support assumption on `N` is required:
zero is not a divisor of a nonzero residue. -/
theorem sum_abs_betaDivisorPart_le (k : ℕ) (N : Finset ℕ) (β : ℕ → ℝ)
    {a : ℤ} (ha : a ≠ 0)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) :
    (∑ n ∈ N, |betaDivisorPart β a n|) ≤
      (fouvryTau (k + 1) a.natAbs : ℝ) := by
  classical
  have ha' : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  calc
    _ = ∑ n ∈ N.filter (fun n : ℕ => (n : ℤ) ∣ a), |β n| := by
      rw [sum_filter]
      apply sum_congr rfl
      intro n _
      simp only [betaDivisorPart]
      split_ifs <;> simp
    _ ≤ ∑ n ∈ N.filter (fun n : ℕ => (n : ℤ) ∣ a), (fouvryTau k n : ℝ) :=
      sum_le_sum (fun n hn => hβ n (mem_filter.mp hn).1)
    _ ≤ ∑ n ∈ a.natAbs.divisors, (fouvryTau k n : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp (mem_filter.mp hn).2, ha'⟩
      · intro n _ _
        positivity
    _ = _ := by rw [fouvryTau_succ, Nat.cast_sum]

/-- A single constant works for all changing sequences and residues of
size at most `x`. In particular the beta order may be zero. -/
theorem sum_abs_betaDivisorPart_uniform_rpow (k : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ∀ a : ℤ, a ≠ 0 → (a.natAbs : ℝ) ≤ x →
      ∀ N : Finset ℕ, ∀ β : ℕ → ℝ,
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∑ n ∈ N, |betaDivisorPart β a n|) ≤ C * x ^ δ := by
  obtain ⟨C, hC, hbound⟩ := fouvryTau_le_const_rpow (k := k + 1) (by omega) hδ
  refine ⟨C, hC, fun x _ a ha hax N β hβ => ?_⟩
  apply (sum_abs_betaDivisorPart_le k N β ha hβ).trans
  apply (hbound a.natAbs (Int.natAbs_pos.mpr ha)).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hax hδ.le) hC.le

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
