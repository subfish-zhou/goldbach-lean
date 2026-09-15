import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Analysis.Real.Sqrt
import MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-!
# Iwaniec's numerical admissibility and lower-endpoint allocation

The numerical conditions are those defining `𝒟⁺` and `𝒟⁻` on p. 311 of
H. Iwaniec, *A new form of the error term in the linear sieve* (1980),
as checked in the right page of `pages/iwaniec-3.png`. The empty sequence
is admitted, as stipulated at the bottom of that page.

Here `b` assigns the **lower endpoint** to each label. Geometric-grid membership
is deliberately separate from these numerical conditions. With zero-based
indexing, upper (`true`) cubic tests occur at even indices, and lower (`false`)
tests occur at odd indices. The head restriction is retained for both sides.

The strict prefix-square estimate proves the numerical input to the two-box
induction of Lemma 1, p. 312 (`pages/iwaniec-4.png`, left page). The resulting
partition preserves occurrences, including repeated labels. No assertion that
the two subsequences retain the original parity conditions is made here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility

open LiLiuPrereqWFBoxAllocation

variable {ι : Type*}

/-- The p. 311 cubic test, with upper/even and lower/odd zero-based parity. -/
def CubicPrefixBound (upper : Bool) (b : ι → ℝ) (D : ℝ) (input : List ι) : Prop :=
  ∀ (i : ℕ) (hi : i < input.length),
    i % 2 = (if upper then 0 else 1) →
      ((input.take i).map b).prod * b input[i] ^ 3 < D

/-- The upper condition is exactly the source's tests at one-based `2ℓ + 1`. -/
theorem cubicPrefixBound_upper_iff (b : ι → ℝ) (D : ℝ) (input : List ι) :
    CubicPrefixBound true b D input ↔
      ∀ (ℓ : ℕ) (hℓ : 2 * ℓ < input.length),
        ((input.take (2 * ℓ)).map b).prod * b input[2 * ℓ] ^ 3 < D := by
  constructor
  · intro h ℓ hℓ
    exact h (2 * ℓ) hℓ (by simp)
  · intro h i hi hpar
    have heq : i = 2 * (i / 2) := by
      change i % 2 = 0 at hpar
      omega
    have hbound : 2 * (i / 2) < input.length := by omega
    simpa only [← heq] using h (i / 2) hbound

/-- The lower condition is exactly the source's tests at one-based `2ℓ`,
with `ℓ ≥ 1`, not at the upper side's odd one-based indices. -/
theorem cubicPrefixBound_lower_iff (b : ι → ℝ) (D : ℝ) (input : List ι) :
    CubicPrefixBound false b D input ↔
      ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ (hℓ : 2 * ℓ - 1 < input.length),
        ((input.take (2 * ℓ - 1)).map b).prod * b input[2 * ℓ - 1] ^ 3 < D := by
  constructor
  · intro h ℓ hpos hℓ
    apply h (2 * ℓ - 1) hℓ
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · intro h i hi hpar
    have heq : i = 2 * (i / 2 + 1) - 1 := by
      simp only [Bool.false_eq_true, ↓reduceIte] at hpar
      omega
    have hbound : 2 * (i / 2 + 1) - 1 < input.length := by omega
    simpa only [← heq] using h (i / 2 + 1) (by omega) hbound

/-- Actual numerical admissibility of a decreasing lower-endpoint sequence.
The fields are the source's inequalities, not an allocation or prefix-square
conclusion. All four conditions are vacuous on the empty sequence. -/
structure Admissible (upper : Bool) (b : ι → ℝ) (D : ℝ) (input : List ι) : Prop where
  one_le : ∀ a ∈ input, 1 ≤ b a
  decreasing : ∀ (i j : ℕ) (hi : i < input.length) (hj : j < input.length),
    i ≤ j → b input[j] ≤ b input[i]
  head_lt_sqrt : ∀ (h : 0 < input.length), b input[0] < Real.sqrt D
  cubic : CubicPrefixBound upper b D input

@[simp]
theorem admissible_nil (upper : Bool) (b : ι → ℝ) (D : ℝ) :
    Admissible upper b D [] := by
  constructor
  · simp
  · intro i j hi
    simp at hi
  · intro h
    simp at h
  · intro i hi
    simp at hi

variable {upper : Bool} {b : ι → ℝ} {D : ℝ} {input : List ι}

/-- The source head restriction and its squared form are equivalent; the
lower-endpoint assumption supplies the necessary nonnegative head. -/
theorem head_lt_sqrt_iff_sq_lt (hone : ∀ a ∈ input, 1 ≤ b a)
    (h : 0 < input.length) :
    b input[0] < Real.sqrt D ↔ b input[0] ^ 2 < D :=
  Real.lt_sqrt (le_trans (by norm_num) (hone _ (List.getElem_mem h)))

theorem Admissible.head_sq_lt (h : Admissible upper b D input)
    (hinput : 0 < input.length) : b input[0] ^ 2 < D :=
  (head_lt_sqrt_iff_sq_lt h.one_le hinput).mp (h.head_lt_sqrt hinput)

theorem Admissible.prefix_prod_nonneg (h : Admissible upper b D input) (i : ℕ) :
    0 ≤ ((input.take i).map b).prod := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact le_trans (by norm_num) (h.one_le a (List.mem_of_mem_take ha))

/-- Every indexed prefix satisfies the strict square budget on the lower
endpoints. At a cubic index use `bᵢ ≥ 1`; at the following index use
`bᵢ ≤ bᵢ₋₁`. The lower side's initial index uses the separate head bound. -/
theorem Admissible.prefix_square_lt (h : Admissible upper b D input)
    (i : ℕ) (hi : i < input.length) :
    ((input.take i).map b).prod * b input[i] ^ 2 < D := by
  by_cases hpar : i % 2 = (if upper then 0 else 1)
  · have hone := h.one_le _ (List.getElem_mem hi)
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone (by omega))
        (h.prefix_prod_nonneg i))
      (h.cubic i hi hpar)
  · cases i with
    | zero => simpa using h.head_sq_lt hi
    | succ j =>
        have hj : j < input.length := by omega
        have hprev : j % 2 = (if upper then 0 else 1) := by
          cases upper <;> simp_all <;> omega
        have hcur0 : 0 ≤ b input[j + 1] :=
          le_trans (by norm_num) (h.one_le _ (List.getElem_mem hi))
        have hprev0 : 0 ≤ b input[j] :=
          le_trans (by norm_num) (h.one_le _ (List.getElem_mem hj))
        have hsq : b input[j + 1] ^ 2 ≤ b input[j] ^ 2 :=
          (sq_le_sq₀ hcur0 hprev0).mpr (h.decreasing j (j + 1) hj hi (by omega))
        calc
          ((input.take (j + 1)).map b).prod * b input[j + 1] ^ 2 =
              (((input.take j).map b).prod * b input[j]) * b input[j + 1] ^ 2 := by
            rw [List.take_succ_eq_append_getElem hj]
            simp only [List.map_append, List.map_singleton, List.prod_append,
              List.prod_singleton]
          _ ≤ (((input.take j).map b).prod * b input[j]) * b input[j] ^ 2 :=
            mul_le_mul_of_nonneg_left hsq
              (mul_nonneg (h.prefix_prod_nonneg j) hprev0)
          _ = ((input.take j).map b).prod * b input[j] ^ 3 := by ring
          _ < D := h.cubic j hj hprev

/-- Numerical admissibility supplies the existing allocation module's budget,
without assuming any prefix-square or allocation statement. -/
theorem Admissible.prefixSquareBound (h : Admissible upper b D input) :
    PrefixSquareBound b D input :=
  fun i hi => (h.prefix_square_lt i hi).le

/-- Allocate every labeled occurrence to exactly one box for any factorization
of the level. Products are of the lower endpoints `b`, not upper endpoints. -/
theorem Admissible.exists_boxPartition (h : Admissible upper b D input)
    {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hMN : M * N = D) :
    ∃ left right : List ι, BoxPartition left right input ∧
      (left.map b).prod ≤ M ∧ (right.map b).prod ≤ N := by
  apply exists_boxPartition_of_prefixSquareBound b hM hN input
  simpa only [hMN] using h.prefixSquareBound

/-- Expanded allocation interface, including subsequence, permutation, and
product identities; repeated labels remain distinct occurrences. -/
theorem Admissible.exists_boxPartition_with_properties (h : Admissible upper b D input)
    {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hMN : M * N = D) :
    ∃ left right : List ι, BoxPartition left right input ∧
      left.Sublist input ∧ right.Sublist input ∧ (left ++ right).Perm input ∧
      (left.map b).prod * (right.map b).prod = (input.map b).prod ∧
      (left.map b).prod ≤ M ∧ (right.map b).prod ≤ N := by
  obtain ⟨left, right, hpart, hleft, hright⟩ := h.exists_boxPartition hM hN hMN
  exact ⟨left, right, hpart, hpart.sublists.1, hpart.sublists.2, hpart.perm,
    hpart.prod_eq b, hleft, hright⟩

end MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility
