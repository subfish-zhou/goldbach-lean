import Mathlib.Data.Finset.Sort
import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser

/-!
# Rounded cubic tests with the source's occurrence indexing

Iwaniec's p. 311 admissibility tests use decreasing lower endpoints and
zero-based parity; the finite Rosser tests on p. 313 use inclusive prime
prefixes and their cardinality. This module identifies these tests by sorting
the original natural-number labels, never their endpoint values. Thus equal
values of `b` keep distinct slots in every mapped prefix product.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open LiLiuPrereqWFAdmissibility

/-- Inclusive decreasing-prime prefixes, evaluated at rounded endpoints.
The parity is one-based: odd for the upper side, even for the lower side. -/
def RoundedSetAdmissible (upper : Bool) (b : ℕ → ℝ) (D : ℝ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, (s.filter (fun q => p ≤ q)).card % 2 = (if upper then 1 else 0) →
    (∏ q ∈ s.filter (fun q => p ≤ q), b q) * (b p) ^ 2 < D

@[simp]
theorem roundedSetAdmissible_empty (upper : Bool) (b : ℕ → ℝ) (D : ℝ) :
    RoundedSetAdmissible upper b D ∅ := by
  simp [RoundedSetAdmissible]

/-- The inclusive prime prefix is exactly the first `i + 1` original slots. -/
theorem rounded_prefix_eq_take (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) :
    s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q) =
      ((s.sort (· ≥ ·)).take (i + 1)).toFinset := by
  ext q
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hq, hle⟩
    obtain ⟨j, hj, rfl⟩ :=
      List.mem_iff_getElem.mp ((Finset.mem_sort (· ≥ ·)).mpr hq)
    have hji := (s.sortedGT_sort.getElem_le_getElem_iff).mp hle
    exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
  · intro hq
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hq
    refine ⟨(Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem (by omega)), ?_⟩
    exact s.sortedGT_sort.getElem_le_getElem_iff.mpr (by omega)

theorem rounded_prefix_card (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) :
    (s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q)).card = i + 1 := by
  rw [rounded_prefix_eq_take s i hi,
    List.toFinset_card_of_nodup
      (List.Nodup.sublist (List.take_sublist _ _) (s.sort_nodup (· ≥ ·)))]
  simp only [List.length_take]
  omega

/-- No injectivity of `b` is needed: the product ranges over prime slots. -/
theorem rounded_prefix_product (b : ℕ → ℝ) (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) :
    (∏ q ∈ s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q), b q) *
        (b (s.sort (· ≥ ·))[i]) ^ 2 =
      (((s.sort (· ≥ ·)).take i).map b).prod *
        (b (s.sort (· ≥ ·))[i]) ^ 3 := by
  rw [rounded_prefix_eq_take s i hi,
    List.prod_toFinset b
      (List.Nodup.sublist (List.take_sublist _ _) (s.sort_nodup (· ≥ ·))),
    List.take_succ_eq_append_getElem hi]
  simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  ring

/-- Exact equivalence of the finite tests with the source's zero-based cubic
tests, including the empty set and coincident endpoint values. -/
theorem roundedSetAdmissible_iff_cubicPrefixBound
    (upper : Bool) (b : ℕ → ℝ) (D : ℝ) (s : Finset ℕ) :
    RoundedSetAdmissible upper b D s ↔
      CubicPrefixBound upper b D (s.sort (· ≥ ·)) := by
  constructor
  · intro h i hi hpar
    have hp : (s.sort (· ≥ ·))[i] ∈ s :=
      (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)
    have hcard : (s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q)).card % 2 =
        (if upper then 1 else 0) := by
      rw [rounded_prefix_card s i hi]
      cases upper <;> simp_all <;> omega
    simpa only [rounded_prefix_product b s i hi] using h _ hp hcard
  · intro h p hp hpar
    obtain ⟨i, hi, rfl⟩ :=
      List.mem_iff_getElem.mp ((Finset.mem_sort (· ≥ ·)).mpr hp)
    rw [rounded_prefix_card s i hi] at hpar
    rw [rounded_prefix_product b s i hi]
    apply h i hi
    cases upper <;> simp_all <;> omega

/-- The numerical side conditions plus finite rounded tests give the actual
source admissibility, with all original prime occurrences retained. -/
theorem roundedSetAdmissible_to_admissible
    {upper : Bool} {b : ℕ → ℝ} {D : ℝ} {s : Finset ℕ}
    (hone : ∀ p ∈ s, 1 ≤ b p)
    (hmono : ∀ p ∈ s, ∀ q ∈ s, p ≤ q → b p ≤ b q)
    (hsq : ∀ p ∈ s, b p ^ 2 < D)
    (h : RoundedSetAdmissible upper b D s) :
    Admissible upper b D (s.sort (· ≥ ·)) := by
  refine ⟨?_, ?_, ?_, (roundedSetAdmissible_iff_cubicPrefixBound upper b D s).mp h⟩
  · intro p hp
    exact hone p ((Finset.mem_sort (· ≥ ·)).mp hp)
  · intro i j hi hj hij
    apply hmono _ ((Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hj))
      _ ((Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi))
    exact s.sortedGT_sort.getElem_le_getElem_iff.mpr hij
  · intro hi
    have hp : (s.sort (· ≥ ·))[0] ∈ s :=
      (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)
    exact (Real.lt_sqrt (le_trans (by norm_num) (hone _ hp))).mpr (hsq _ hp)

theorem roundedSetAdmissible_iff_admissible
    {upper : Bool} {b : ℕ → ℝ} {D : ℝ} {s : Finset ℕ}
    (hone : ∀ p ∈ s, 1 ≤ b p)
    (hmono : ∀ p ∈ s, ∀ q ∈ s, p ≤ q → b p ≤ b q)
    (hsq : ∀ p ∈ s, b p ^ 2 < D) :
    RoundedSetAdmissible upper b D s ↔
      Admissible upper b D (s.sort (· ≥ ·)) :=
  ⟨roundedSetAdmissible_to_admissible hone hmono hsq,
    fun h => (roundedSetAdmissible_iff_cubicPrefixBound upper b D s).mpr h.cubic⟩

/-- Mapping endpoints does not remove equal entries. -/
theorem rounded_sorted_map_length (b : ℕ → ℝ) (s : Finset ℕ) :
    ((s.sort (· ≥ ·)).map b).length = s.card := by
  simp

theorem roundedSetAdmissible_cast_lower_iff (D : ℝ) (s : Finset ℕ) :
    RoundedSetAdmissible false (fun p : ℕ => (p : ℝ)) D s ↔
      SmallRosser.LowerAdmissibleSet D s := by
  simp only [RoundedSetAdmissible, SmallRosser.LowerAdmissibleSet,
    Bool.false_eq_true, ↓reduceIte, Nat.even_iff, Nat.cast_prod, id_eq]

theorem roundedSetAdmissible_cast_upper_iff (D : ℝ) (s : Finset ℕ) :
    RoundedSetAdmissible true (fun p : ℕ => (p : ℝ)) D s ↔
      SmallRosser.UpperAdmissibleSet D s := by
  simp only [RoundedSetAdmissible, SmallRosser.UpperAdmissibleSet,
    ↓reduceIte, Nat.not_even_iff_odd, Nat.odd_iff, Nat.cast_prod, id_eq]

end MathlibNt.SieveTheory.LiLiuPrereqWF
