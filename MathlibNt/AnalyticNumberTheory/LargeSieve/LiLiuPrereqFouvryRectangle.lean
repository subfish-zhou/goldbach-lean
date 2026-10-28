import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finite rectangular partial summation

The coefficients in this file are completely arbitrary. In particular, arithmetic
coefficients, phases, and nonrectangular support indicators belong in `a`, not in
the weight. The difference kernel is the tensor product of forward differences,
with the weight extended by zero outside the box.
-/

open scoped BigOperators

namespace LiLiuPrereqFouvry.Rectangle

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- Closed natural-number box, including empty and singleton intervals. -/
noncomputable def box (lo hi : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc (lo i) (hi i))

@[simp] theorem mem_box (lo hi x : ι → ℕ) :
    x ∈ box lo hi ↔ ∀ i, lo i ≤ x i ∧ x i ≤ hi i := by
  simp [box]

/-- One coordinate of the zero-extended forward difference. -/
def differenceKernel (t u : ℕ) : ℂ :=
  (if t = u then 1 else 0) - (if t + 1 = u then 1 else 0)

/-- Full mixed forward difference, with all upper faces anchored at zero. -/
noncomputable def mixedDifference (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ)
    (t : ι → ℕ) : ℂ :=
  ∑ u ∈ box lo hi, w u * ∏ i, differenceKernel (t i) (u i)


/-- Total anchored mixed finite-difference variation. -/
noncomputable def variation (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ) : ℝ :=
  ∑ t ∈ box lo hi, ‖mixedDifference lo hi w t‖


theorem box_eq_empty_iff (lo hi : ι → ℕ) :
    box lo hi = ∅ ↔ ∃ i, hi i < lo i := by
  classical
  simp [box, Fintype.piFinset_eq_empty]

private theorem sum_differenceKernel (x h u : ℕ) (hxh : x ≤ h) (huh : u ≤ h) :
    (∑ t ∈ Finset.Icc x h, differenceKernel t u) =
      if x = u then 1 else 0 := by
  have ht := Finset.sum_Icc_sub hxh (fun t => (if t = u then 1 else 0 : ℂ))
  have hne : h + 1 ≠ u := by omega
  simp only [hne, ↓reduceIte, zero_sub] at ht
  simp only [differenceKernel, Finset.sum_sub_distrib] at *
  linear_combination -ht

private theorem prod_eq_indicator (x u : ι → ℕ) :
    (∏ i, (if x i = u i then 1 else 0 : ℂ)) =
      if x = u then 1 else 0 := by
  classical
  by_cases h : x = u
  · subst u
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ u i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem sum_tensorKernel (x hi u : ι → ℕ)
    (hx : ∀ i, x i ≤ hi i) (hu : ∀ i, u i ≤ hi i) :
    (∑ t ∈ box x hi, ∏ i, differenceKernel (t i) (u i)) =
      if x = u then 1 else 0 := by
  classical
  rw [box, ← Finset.prod_univ_sum (fun i => Finset.Icc (x i) (hi i))
    (fun i t => differenceKernel t (u i))]
  simp_rw [sum_differenceKernel _ _ _ (hx _) (hu _)]
  exact prod_eq_indicator x u

/-- The mixed differences telescope on every upper subrectangle. -/
theorem reconstruct (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ) (x : ι → ℕ)
    (hx : x ∈ box lo hi) :
    (∑ t ∈ box x hi, mixedDifference lo hi w t) = w x := by
  classical
  simp only [mixedDifference]
  rw [Finset.sum_comm]
  have hx' := (mem_box lo hi x).mp hx
  calc
    (∑ u ∈ box lo hi, ∑ t ∈ box x hi,
        w u * ∏ i, differenceKernel (t i) (u i)) =
        ∑ u ∈ box lo hi, w u * (if x = u then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum, sum_tensorKernel x hi u
        (fun i => (hx' i).2) (fun i => ((mem_box lo hi u).mp hu i).2)]
    _ = w x := by simp [hx]


/-- The upper vertex selected by a Boolean choice in every coordinate. -/
def corner (t : ι → ℕ) (e : ι → Bool) : ι → ℕ :=
  fun i => t i + if e i then 1 else 0

/-- Alternating sign of a cube vertex. -/
def cornerSign (e : ι → Bool) : ℂ :=
  ∏ i, if e i then (-1 : ℂ) else 1

/-- Extension by zero only concerns the weight outside its enclosing box. -/
noncomputable def extendWeight (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ)
    (x : ι → ℕ) : ℂ :=
  if x ∈ box lo hi then w x else 0

private theorem differenceKernel_bool (t u : ℕ) :
    differenceKernel t u =
      ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
        (if u = t + (if b then 1 else 0) then 1 else 0) := by
  simp [differenceKernel, eq_comm, sub_eq_add_neg, add_comm]
  split_ifs <;> norm_num

private theorem tensorKernel_corners (t u : ι → ℕ) :
    (∏ i, differenceKernel (t i) (u i)) =
      ∑ e : ι → Bool, cornerSign e * (if u = corner t e then 1 else 0) := by
  classical
  simp_rw [differenceKernel_bool]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.prod_mul_distrib]
  change cornerSign e * (∏ i, if u i = corner t e i then (1 : ℂ) else 0) = _
  rw [prod_eq_indicator]

/-- The kernel definition is exactly the usual alternating `2^d`-corner stencil.
At an upper face, the zero extension produces the lower-order face difference. -/
theorem mixedDifference_eq_corners (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ)
    (t : ι → ℕ) :
    mixedDifference lo hi w t =
      ∑ e : ι → Bool, cornerSign e * extendWeight lo hi w (corner t e) := by
  classical
  unfold mixedDifference
  simp_rw [tensorKernel_corners, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ u ∈ box lo hi, w u * (cornerSign e * if u = corner t e then 1 else 0)) =
        cornerSign e * (∑ u ∈ box lo hi, w u * if u = corner t e then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = cornerSign e * extendWeight lo hi w (corner t e) := by
      simp [extendWeight]


end LiLiuPrereqFouvry.Rectangle
