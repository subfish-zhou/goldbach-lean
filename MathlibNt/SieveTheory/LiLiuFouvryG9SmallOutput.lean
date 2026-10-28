import MathlibNt.SieveTheory.LiLiuFouvryG9MotherSieve

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- Sum all small fibres; the range starts at zero and labels need not be injective. -/
theorem g9SmallOutput_fibre_sum {ι : Type*} (S : Finset ι) (a : ι → ℕ)
    (w : ι → ℝ) (z J : ℝ)
    (hf : ∀ r ∈ range ⌈z⌉₊, (∑ x ∈ S, if a x = r then w x else 0) ≤ J) :
    (∑ x ∈ S, w x * (if (a x : ℝ) < z then 1 else 0)) ≤ (⌈z⌉₊ : ℝ)*J := by
  classical
  have heq : ∀ x ∈ S, w x * (if (a x : ℝ) < z then 1 else 0) =
      ∑ r ∈ range ⌈z⌉₊, if a x = r then w x else 0 := by
    intro x _
    by_cases h : (a x : ℝ) < z
    · rw [if_pos h, mul_one]
      symm
      rw [sum_eq_single (a x)]
      · simp
      · intro r _ hr
        simp [Ne.symm hr]
      · intro hn
        exact False.elim (hn (mem_range.mpr (Nat.lt_ceil.mpr h)))
    · rw [if_neg h, mul_zero]
      symm
      apply sum_eq_zero
      intro r hr
      apply if_neg
      intro ha
      apply h
      rw [ha]
      exact Nat.lt_ceil.mp (mem_range.mp hr)
  calc
    _ = ∑ x ∈ S, ∑ r ∈ range ⌈z⌉₊, if a x = r then w x else 0 := sum_congr rfl heq
    _ = ∑ r ∈ range ⌈z⌉₊, ∑ x ∈ S, if a x = r then w x else 0 := sum_comm
    _ ≤ ∑ _r ∈ range ⌈z⌉₊, J := sum_le_sum hf
    _ = _ := by simp


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
