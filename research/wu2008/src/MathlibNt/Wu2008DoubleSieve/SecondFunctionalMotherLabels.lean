import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherCarriers

/-! # Literal finite label inequality for all four prime bands -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

def secondFunctionalMotherPrefixIndices : List ℕ :=
  [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]

noncomputable def secondFunctionalMotherGammaLabels (s : Finset ℕ) (χ : ℕ → ℕ) (i : ℕ) : ℕ :=
  ((secondFunctionalMotherGammaWords i).map fun cs => (fourthRowMotherColoured s χ cs).card).sum

theorem secondFunctionalMother_gamma_labels (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 3) (i : ℕ) :
    secondFunctionalMotherGammaLabels s χ i =
      secondFunctionalMotherGammaBand (fourthRowMotherColourCount s χ 0)
        (fourthRowMotherColourCount s χ 1) (fourthRowMotherColourCount s χ 2)
        (fourthRowMotherColourCount s χ 3) i := by
  simp only [secondFunctionalMotherGammaLabels, secondFunctionalMotherGammaBand,
    secondFunctionalMother_coloured_card s χ hχ hcap]

theorem secondFunctionalMother_mid_band_card (s : Finset ℕ) (χ : ℕ → ℕ) :
    (s.filter fun p => χ p ≤ 2).card = fourthRowMotherColourCount s χ 0 +
      fourthRowMotherColourCount s χ 1 + fourthRowMotherColourCount s χ 2 := by
  have he : (s.filter fun p => χ p ≤ 2) =
      (s.filter fun p => χ p ≤ 1) ∪ (s.filter fun p => χ p = 2) := by
    ext p
    simp only [mem_filter, mem_union]
    have he : χ p ≤ 2 ↔ χ p ≤ 1 ∨ χ p = 2 := by omega
    tauto
  rw [he, card_union_of_disjoint, fourthRowMother_low_band_card]
  · rfl
  · simp only [disjoint_left, mem_filter]
    omega

noncomputable def secondFunctionalMotherLabelWeight (s : Finset ℕ) (χ : ℕ → ℕ) : ℝ :=
  4 + (if (s.filter fun p => χ p = 0) = ∅ then 1 else 0) - (s.card : ℝ) -
    ((s.filter fun p => χ p ≤ 1).card : ℝ) - ((s.filter fun p => χ p ≤ 2).card : ℝ) +
    ((fourthRowMotherLowPairs s χ).card : ℝ) + ((fourthRowMotherCrossPairs s χ).card : ℝ) +
    (secondFunctionalMotherPrefixIndices.map fun i =>
      (secondFunctionalMotherGammaLabels s χ i : ℝ)).sum

theorem secondFunctionalMother_label_weight_eq (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 3) :
    secondFunctionalMotherLabelWeight s χ =
      secondFunctionalMotherScalar (fourthRowMotherColourCount s χ 0)
        (fourthRowMotherColourCount s χ 1) (fourthRowMotherColourCount s χ 2)
        (fourthRowMotherColourCount s χ 3) := by
  have hc := secondFunctionalMother_colour_count_sum s χ hcap
  have he : (s.filter fun p => χ p = 0) = ∅ ↔ fourthRowMotherColourCount s χ 0 = 0 :=
    card_eq_zero.symm
  simp only [secondFunctionalMotherLabelWeight, he, ← hc, fourthRowMother_low_band_card,
    secondFunctionalMother_mid_band_card, fourthRowMother_low_pairs_card,
    fourthRowMother_cross_pairs_card, secondFunctionalMother_gamma_labels s χ hχ hcap,
    secondFunctionalMotherPrefixIndices, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil,
    secondFunctionalMother_gamma7_formula,
    secondFunctionalMother_gamma8_formula,
    secondFunctionalMother_gamma9_formula,
    secondFunctionalMother_gamma10_formula,
    secondFunctionalMother_gamma11_formula,
    secondFunctionalMother_gamma12_formula,
    secondFunctionalMother_gamma13_formula,
    secondFunctionalMother_gamma14_formula,
    secondFunctionalMother_gamma15_formula,
    secondFunctionalMother_gamma16_formula,
    secondFunctionalMother_gamma17_formula,
    secondFunctionalMother_gamma18_formula,
    secondFunctionalMother_gamma19_formula,
    secondFunctionalMother_gamma20_formula,
    secondFunctionalMother_gamma21_formula,
    secondFunctionalMotherScalar, Nat.cast_add, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero]
  ring

theorem secondFunctionalMother_label_weight (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 3) :
    (if s = ∅ then (5 : ℝ) else 0) ≤ secondFunctionalMotherLabelWeight s χ := by
  rw [secondFunctionalMother_label_weight_eq s χ hχ hcap]
  have hc := secondFunctionalMother_colour_count_sum s χ hcap
  have he : s = ∅ ↔ fourthRowMotherColourCount s χ 0 + fourthRowMotherColourCount s χ 1 +
      fourthRowMotherColourCount s χ 2 + fourthRowMotherColourCount s χ 3 = 0 := by
    rw [hc, card_eq_zero]
  simpa only [he] using secondFunctionalMother_scalar
    (fourthRowMotherColourCount s χ 0) (fourthRowMotherColourCount s χ 1)
    (fourthRowMotherColourCount s χ 2) (fourthRowMotherColourCount s χ 3)

end Wu2008DoubleSieve
