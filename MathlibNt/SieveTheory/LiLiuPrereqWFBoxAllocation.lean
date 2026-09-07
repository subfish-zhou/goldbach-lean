import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The numerical two-box allocation core

This is the finite numerical induction in the proof of Lemma 1, p. 312, of
H. Iwaniec, *A new form of the error term in the linear sieve* (1980).
It does not assert the full lemma's admissibility geometry or construct sieve weights.

Every occurrence is assigned to exactly one box, in its original order. The input may
carry arbitrary labels, with a real weight attached to each label. In fact the numerical
argument does not require the weights to be nonnegative.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

variable {α : Type*}

/-- An occurrence-preserving partition into two subsequences. Each constructor puts
the new final occurrence in exactly one of the boxes, even when labels repeat. -/
inductive BoxPartition : List α → List α → List α → Prop
  | nil : BoxPartition [] [] []
  | left {left right input : List α} (a : α) :
      BoxPartition left right input →
      BoxPartition (left ++ [a]) right (input ++ [a])
  | right {left right input : List α} (a : α) :
      BoxPartition left right input →
      BoxPartition left (right ++ [a]) (input ++ [a])

theorem BoxPartition.sublists {left right input : List α}
    (h : BoxPartition left right input) : left.Sublist input ∧ right.Sublist input := by
  induction h with
  | nil => exact ⟨List.Sublist.refl [], List.Sublist.refl []⟩
  | @left left right input a h ih =>
      exact ⟨ih.1.append_right [a],
        ih.2.trans (List.sublist_append_left input [a])⟩
  | @right left right input a h ih =>
      exact ⟨ih.1.trans (List.sublist_append_left input [a]),
        ih.2.append_right [a]⟩

theorem BoxPartition.perm {left right input : List α}
    (h : BoxPartition left right input) : (left ++ right).Perm input := by
  induction h with
  | nil => exact List.Perm.refl []
  | @left left right input a h ih =>
      have hswap := (List.perm_append_comm (l₁ := [a]) (l₂ := right)).append_left left
      have htail := ih.append_right [a]
      have hswap' : ((left ++ [a]) ++ right).Perm ((left ++ right) ++ [a]) := by
        simpa only [List.append_assoc] using hswap
      exact hswap'.trans htail
  | @right left right input a h ih =>
      simpa only [List.append_assoc] using ih.append_right [a]

theorem BoxPartition.prod_eq {left right input : List α}
    (h : BoxPartition left right input) (weight : α → ℝ) :
    (left.map weight).prod * (right.map weight).prod = (input.map weight).prod := by
  induction h with
  | nil => simp
  | left a h ih =>
      simpa only [List.map_append, List.map_singleton, List.prod_append,
        List.prod_singleton, mul_assoc, mul_comm, mul_left_comm] using
        congrArg (fun p : ℝ => p * weight a) ih
  | right a h ih =>
      simpa only [List.map_append, List.map_singleton, List.prod_append,
        List.prod_singleton, mul_assoc] using
        congrArg (fun p : ℝ => p * weight a) ih

/-- If appending a factor overflowed both boxes, the squared-factor budget would
be exceeded. No sign assumption on the box products or factor is necessary. -/
theorem append_fits_one_box {A B x M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hbudget : (A * B) * x ^ 2 ≤ M * N) : A * x ≤ M ∨ B * x ≤ N := by
  by_contra h
  push Not at h
  have hstrict : M * N < (A * x) * (B * x) := calc
    M * N ≤ M * (B * x) := mul_le_mul_of_nonneg_left h.2.le hM
    _ < (A * x) * (B * x) :=
      mul_lt_mul_of_pos_right h.1 (lt_of_le_of_lt hN h.2)
  have heq : (A * x) * (B * x) = (A * B) * x ^ 2 := by ring
  rw [heq] at hstrict
  exact (not_lt_of_ge hbudget) hstrict

/-- The actual indexed-prefix squared-factor condition, not an allocation premise. -/
def PrefixSquareBound (weight : α → ℝ) (D : ℝ) (input : List α) : Prop :=
  ∀ (i : ℕ) (hi : i < input.length),
    ((input.take i).map weight).prod * weight input[i] ^ 2 ≤ D

/-- Bridge between the indexed condition and the step used by the snoc induction. -/
theorem prefixSquareBound_append_singleton_iff (weight : α → ℝ) (D : ℝ)
    (input : List α) (a : α) :
    PrefixSquareBound weight D (input ++ [a]) ↔
      PrefixSquareBound weight D input ∧
        (input.map weight).prod * weight a ^ 2 ≤ D := by
  constructor
  · intro h
    constructor
    · intro i hi
      have h' := h i (by simpa using Nat.lt_succ_of_lt hi)
      simpa only [List.take_append_of_le_length hi.le, List.getElem_append_left hi] using h'
    · have h' := h input.length (by simp)
      simpa [List.getElem_append_right] using h'
  · rintro ⟨hprefix, hlast⟩ i hi
    by_cases hlt : i < input.length
    · simpa only [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt] using
        hprefix i hlt
    · have heq : i = input.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      simpa [List.getElem_append_right] using hlast

/-- Construct the two boxes by appending each occurrence to a box that fits.
This is the numerical core only, with no sieve-support or parity assertion. -/
theorem exists_boxPartition_of_prefixSquareBound (weight : α → ℝ) {M N : ℝ}
    (hM : 1 ≤ M) (hN : 1 ≤ N) (input : List α)
    (hprefix : PrefixSquareBound weight (M * N) input) :
    ∃ left right : List α, BoxPartition left right input ∧
      (left.map weight).prod ≤ M ∧ (right.map weight).prod ≤ N := by
  induction input using List.reverseRecOn with
  | nil => exact ⟨[], [], BoxPartition.nil, by simpa using hM, by simpa using hN⟩
  | append_singleton input a ih =>
      obtain ⟨hprefix, hlast⟩ :=
        (prefixSquareBound_append_singleton_iff weight (M * N) input a).mp hprefix
      obtain ⟨left, right, hpart, hleft, hright⟩ := ih hprefix
      rw [← hpart.prod_eq weight] at hlast
      rcases append_fits_one_box (by linarith : 0 ≤ M) (by linarith : 0 ≤ N) hlast with
        hfits | hfits
      · exact ⟨left ++ [a], right, hpart.left a,
          by simpa using hfits, hright⟩
      · exact ⟨left, right ++ [a], hpart.right a,
          hleft, by simpa using hfits⟩

/-- Real-list form with the explicit indexed hypothesis and the usual sublist,
permutation, and product conclusions. The partition witness records disjoint
occurrences; disjointness of values is neither required nor appropriate. -/
theorem exists_real_box_partition {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (input : List ℝ)
    (hprefix : ∀ (i : ℕ) (hi : i < input.length),
      (input.take i).prod * input[i] ^ 2 ≤ M * N) :
    ∃ left right : List ℝ, BoxPartition left right input ∧
      left.Sublist input ∧ right.Sublist input ∧ (left ++ right).Perm input ∧
      left.prod * right.prod = input.prod ∧ left.prod ≤ M ∧ right.prod ≤ N := by
  have hbound : PrefixSquareBound id (M * N) input := by
    simpa only [PrefixSquareBound, List.map_id, id_eq] using hprefix
  obtain ⟨left, right, hpart, hleft, hright⟩ :=
    exists_boxPartition_of_prefixSquareBound id hM hN input hbound
  refine ⟨left, right, hpart, hpart.sublists.1, hpart.sublists.2, hpart.perm, ?_, ?_, ?_⟩
  · simpa using hpart.prod_eq id
  · simpa using hleft
  · simpa using hright

end MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
