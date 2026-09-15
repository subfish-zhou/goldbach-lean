import MathlibNt.Wu2008DoubleSieve.FourthRowMotherBandFormulas
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherCarriers

/-! # Exact distinct-factor label weight, with all surviving triple addends -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_low_band_card (s : Finset ℕ) (χ : ℕ → ℕ) :
    (s.filter (fun p => χ p ≤ 1)).card =
      fourthRowMotherColourCount s χ 0 + fourthRowMotherColourCount s χ 1 := by
  have he : s.filter (fun p => χ p ≤ 1) =
      s.filter (fun p => χ p = 0) ∪ s.filter (fun p => χ p = 1) := by
    ext p
    simp only [mem_filter, mem_union]
    have he : χ p ≤ 1 ↔ χ p = 0 ∨ χ p = 1 := by omega
    rw [he, and_or_left]
  rw [he, card_union_of_disjoint]
  · rfl
  · apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    omega

noncomputable def fourthRowMotherLowPairs (s : Finset ℕ) (χ : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  ((s.filter fun p => χ p ≤ 1) ×ˢ (s.filter fun p => χ p ≤ 1)).filter fun p => p.1 < p.2

theorem fourthRowMother_low_pairs_card (s : Finset ℕ) (χ : ℕ → ℕ) :
    (fourthRowMotherLowPairs s χ).card =
      (fourthRowMotherColourCount s χ 0 + fourthRowMotherColourCount s χ 1).choose 2 := by
  rw [fourthRowMotherLowPairs, card_product_filter_lt, fourthRowMother_low_band_card]

noncomputable def fourthRowMotherCrossPairs (s : Finset ℕ) (χ : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (s.filter fun p => χ p = 0) ×ˢ (s.filter fun p => χ p = 2)

theorem fourthRowMother_cross_pairs_card (s : Finset ℕ) (χ : ℕ → ℕ) :
    (fourthRowMotherCrossPairs s χ).card =
      fourthRowMotherColourCount s χ 0 * fourthRowMotherColourCount s χ 2 :=
  card_product _ _

theorem fourthRowMother_cross_pairs_order {s : Finset ℕ} {χ : ℕ → ℕ}
    (hχ : Monotone χ) {p q : ℕ} (hpq : (p, q) ∈ fourthRowMotherCrossPairs s χ) :
    p < q := by
  obtain ⟨hp, hq⟩ := mem_product.mp hpq
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  change χ p = 0 at hp'
  change χ q = 2 at hq'
  by_contra h
  have hh := hχ (show q ≤ p by omega)
  omega

noncomputable def fourthRowMotherLabelWeight (s : Finset ℕ) (χ : ℕ → ℕ) : ℝ :=
  4 + (if (s.filter fun p => χ p = 0) = ∅ then 1 else 0) -
    2 * (s.card : ℝ) - ((s.filter fun p => χ p ≤ 1).card : ℝ) +
    ((fourthRowMotherLowPairs s χ).card : ℝ) +
    ((fourthRowMotherCrossPairs s χ).card : ℝ) +
    ((fourthRowMotherColoured s χ [0, 0]).card : ℝ) +
    ((fourthRowMotherColoured s χ [0, 1]).card : ℝ) +
    (((fourthRowMotherColoured s χ [1, 1, 1]).card +
      (fourthRowMotherColoured s χ [1, 1, 2]).card +
      (fourthRowMotherColoured s χ [1, 2, 2]).card +
      (fourthRowMotherColoured s χ [2, 2, 2]).card : ℕ) : ℝ) +
    ((fourthRowMotherColoured s χ [1, 1, 2]).card : ℝ) +
    ((fourthRowMotherColoured s χ [1, 2, 2]).card : ℝ) +
    ((fourthRowMotherColoured s χ [0, 1, 2]).card : ℝ) +
    ((fourthRowMotherColoured s χ [0, 2, 2]).card : ℝ) +
    ((fourthRowMotherColoured s χ [2, 2, 2, 2]).card : ℝ)

theorem fourthRowMother_label_weight_eq (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hbound : ∀ p ∈ s, χ p ≤ 2) :
    fourthRowMotherLabelWeight s χ = fourthRowMotherScalar
      (fourthRowMotherColourCount s χ 0) (fourthRowMotherColourCount s χ 1)
      (fourthRowMotherColourCount s χ 2) := by
  have hc := fourthRowMother_colour_count_sum s χ hbound
  have he : (s.filter fun p => χ p = 0) = ∅ ↔ fourthRowMotherColourCount s χ 0 = 0 :=
    card_eq_zero.symm
  obtain ⟨h00, h01, h112, h122, h012, h022, h2222, h9⟩ := fourthRowMother_band_formulas
    (fourthRowMotherColourCount s χ 0) (fourthRowMotherColourCount s χ 1)
    (fourthRowMotherColourCount s χ 2)
  simp only [fourthRowMotherLabelWeight, he, ← hc, fourthRowMother_low_band_card,
    fourthRowMother_low_pairs_card, fourthRowMother_cross_pairs_card,
    fourthRowMother_coloured_card s χ hχ hbound]
  rw [h9]
  simp only [h00, h01, h112, h122, h012, h022, h2222, Nat.cast_ite,
    Nat.cast_zero, Nat.cast_mul, fourthRowMotherScalar]

theorem fourthRowMother_label_weight (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hbound : ∀ p ∈ s, χ p ≤ 2) :
    (if s = ∅ then (5 : ℝ) else 0) ≤ fourthRowMotherLabelWeight s χ := by
  rw [fourthRowMother_label_weight_eq s χ hχ hbound]
  have hc := fourthRowMother_colour_count_sum s χ hbound
  have he : s = ∅ ↔
      fourthRowMotherColourCount s χ 0 + fourthRowMotherColourCount s χ 1 +
        fourthRowMotherColourCount s χ 2 = 0 := by
    rw [hc, card_eq_zero]
  simpa only [he] using fourthRowMother_scalar
    (fourthRowMotherColourCount s χ 0) (fourthRowMotherColourCount s χ 1)
    (fourthRowMotherColourCount s χ 2)

theorem fourthRowMother_actual_divisor_weight (P : Finset ℕ) (n : ℕ) (b c : ℝ) :
    (if divisorsIn P n = ∅ then (5 : ℝ) else 0) ≤
      fourthRowMotherLabelWeight (divisorsIn P n) (fourthRowMotherColour b c) :=
  fourthRowMother_label_weight _ _ (fourthRowMother_colour_monotone b c)
    (fun p _ => fourthRowMother_colour_le_two b c p)

end Wu2008DoubleSieve
