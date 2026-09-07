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

/-- Unweighted rectangular prefix; `a` may already contain any support mask. -/
noncomputable def rectanglePrefix (lo hi : ι → ℕ) (a : (ι → ℕ) → ℂ)
    (t : ι → ℕ) : ℂ := by
  classical
  exact ∑ x ∈ (box lo hi).filter (fun x => x ≤ t), a x

/-- Total anchored mixed finite-difference variation. -/
noncomputable def variation (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ) : ℝ :=
  ∑ t ∈ box lo hi, ‖mixedDifference lo hi w t‖

/-- Explicit finite maximum of the norms of all rectangular prefixes. -/
noncomputable def prefixMax (lo hi : ι → ℕ) (a : (ι → ℕ) → ℂ) : ℝ :=
  ((box lo hi).sup (fun t => ‖rectanglePrefix lo hi a t‖₊) : NNReal)

/-- These really are rectangular prefixes, with coordinatewise truncation. -/
theorem rectanglePrefix_eq_box_min (lo hi : ι → ℕ) (a : (ι → ℕ) → ℂ)
    (t : ι → ℕ) :
    rectanglePrefix lo hi a t =
      ∑ x ∈ box lo (fun i => min (hi i) (t i)), a x := by
  unfold rectanglePrefix
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_box, Pi.le_def, le_min_iff]
  constructor
  · rintro ⟨hx, hxt⟩ i
    exact ⟨(hx i).1, (hx i).2, hxt i⟩
  · intro hx
    exact ⟨fun i => ⟨(hx i).1, (hx i).2.1⟩, fun i => (hx i).2.2⟩

theorem rectanglePrefix_eq_box (lo hi : ι → ℕ) (a : (ι → ℕ) → ℂ)
    (t : ι → ℕ) (ht : ∀ i, t i ≤ hi i) :
    rectanglePrefix lo hi a t = ∑ x ∈ box lo t, a x := by
  rw [rectanglePrefix_eq_box_min]
  simp only [min_eq_right (ht _)]

@[simp] theorem box_self (x : ι → ℕ) : box x x = {x} := by
  classical
  simp [box, Fintype.piFinset_singleton]

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

private theorem filter_upper_box (lo hi x : ι → ℕ) (hx : x ∈ box lo hi) :
    (box lo hi).filter (fun t => x ≤ t) = box x hi := by
  classical
  ext t
  have hx' := (mem_box lo hi x).mp hx
  simp only [Finset.mem_filter, mem_box, Pi.le_def]
  constructor
  · rintro ⟨ht, hxt⟩ i
    exact ⟨hxt i, (ht i).2⟩
  · intro ht
    exact ⟨fun i => ⟨(hx' i).1.trans (ht i).1, (ht i).2⟩, fun i => (ht i).1⟩

/-- Exact multidimensional summation by parts. Only `w` is differenced. -/
theorem summation_by_parts (lo hi : ι → ℕ) (w a : (ι → ℕ) → ℂ) :
    (∑ x ∈ box lo hi, w x * a x) =
      ∑ t ∈ box lo hi, mixedDifference lo hi w t * rectanglePrefix lo hi a t := by
  classical
  symm
  unfold rectanglePrefix
  simp only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ t ∈ box lo hi, if x ≤ t then mixedDifference lo hi w t * a x else 0) =
        (∑ t ∈ (box lo hi).filter (fun t => x ≤ t),
          mixedDifference lo hi w t) * a x := by
      rw [Finset.sum_mul, Finset.sum_filter]
    _ = w x * a x := by rw [filter_upper_box lo hi x hx, reconstruct lo hi w x hx]

theorem prefix_norm_le_prefixMax (lo hi : ι → ℕ) (a : (ι → ℕ) → ℂ)
    (t : ι → ℕ) (ht : t ∈ box lo hi) :
    ‖rectanglePrefix lo hi a t‖ ≤ prefixMax lo hi a := by
  unfold prefixMax
  exact_mod_cast (Finset.le_sup (f := fun t => ‖rectanglePrefix lo hi a t‖₊) ht)

theorem variation_nonneg (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ) :
    0 ≤ variation lo hi w :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem prefixMax_nonneg (lo hi : ι → ℕ) (a : (ι → ℕ) → ℂ) :
    0 ≤ prefixMax lo hi a :=
  NNReal.coe_nonneg _

/-- Rectangle-prefix inequality with a constructed maximum, not an assumed bound. -/
theorem norm_sum_le_variation_mul_prefixMax (lo hi : ι → ℕ)
    (w a : (ι → ℕ) → ℂ) :
    ‖∑ x ∈ box lo hi, w x * a x‖ ≤ variation lo hi w * prefixMax lo hi a := by
  rw [summation_by_parts]
  calc
    ‖∑ t ∈ box lo hi, mixedDifference lo hi w t * rectanglePrefix lo hi a t‖ ≤
        ∑ t ∈ box lo hi, ‖mixedDifference lo hi w t * rectanglePrefix lo hi a t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ box lo hi, ‖mixedDifference lo hi w t‖ * prefixMax lo hi a := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (prefix_norm_le_prefixMax lo hi a t ht)
        (norm_nonneg _)
    _ = variation lo hi w * prefixMax lo hi a := by
      rw [variation, Finset.sum_mul]

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

/-- The preceding bound applies to any finite, possibly nonrectangular support.
The exact support indicator remains inside each unweighted prefix. -/
theorem norm_sum_masked_le (lo hi : ι → ℕ) (s : Finset (ι → ℕ))
    (hs : s ⊆ box lo hi) (w a : (ι → ℕ) → ℂ) :
    ‖∑ x ∈ s, w x * a x‖ ≤
      variation lo hi w *
        prefixMax lo hi (fun x => if x ∈ s then a x else 0) := by
  classical
  have heq :
      (∑ x ∈ box lo hi, w x * (if x ∈ s then a x else 0)) =
        ∑ x ∈ s, w x * a x := by
    symm
    calc
      (∑ x ∈ s, w x * a x) =
          ∑ x ∈ s, w x * (if x ∈ s then a x else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hx]
      _ = ∑ x ∈ box lo hi, w x * (if x ∈ s then a x else 0) :=
        Finset.sum_subset hs (by intro x _ hx; simp [hx])
  simpa only [heq] using
    norm_sum_le_variation_mul_prefixMax lo hi w (fun x => if x ∈ s then a x else 0)

/-- Five-coordinate specialization for the dispersion consumer. -/
theorem norm_sum_five_le (lo hi : Fin 5 → ℕ) (w a : (Fin 5 → ℕ) → ℂ) :
    ‖∑ x ∈ box lo hi, w x * a x‖ ≤ variation lo hi w * prefixMax lo hi a :=
  norm_sum_le_variation_mul_prefixMax lo hi w a

end LiLiuPrereqFouvry.Rectangle
