import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateProfiles

/-! # Exact natural counts retaining every original convolution tuple -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowTripleNoGateOriginalTuples (N d : ℕ) (δ : ℝ)
    (eleven : Bool) : Finset (List ℕ) :=
  (fourthRowMotherTuples (primeWindow N (wuLocalCutoff N δ d (103 / 25))
    (wuLocalCutoff N δ d (5 / 2))) 3).filter fun l =>
      l.map (fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
        (wuLocalCutoff N δ d (291 / 100))) = fourthRowTripleNoGateWord eleven

noncomputable def fourthRowTripleNoGateOriginalLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) :
    Finset (Σ _ : Fin i → ℕ, Σ _ : List ℕ, ℕ) :=
  (Fintype.piFinset W).sigma fun t =>
    (fourthRowTripleNoGateOriginalTuples N (∏ j, t j) δ eleven).sigma
      (fourthRowMotherPrefixCarrier N (∏ j, t j))

theorem fourthRowTripleNoGate_natural_card {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) :
    (Nat.card {a // a ∈ fourthRowTripleNoGateOriginalLabels N δ W eleven} : ℝ) =
      fourthRowMotherPrefixSum N δ W (fourthRowTripleNoGateWord eleven) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simp only [fourthRowTripleNoGateOriginalLabels, card_sigma, Nat.cast_sum,
    fourthRowMotherPrefixSum, boxConvolution_sum_fibres, fourthRowMotherPrefixTerm,
    fourthRowTripleNoGateOriginalTuples, sum_filter, Nat.cast_ite, Nat.cast_zero]
  rfl

end Wu2008DoubleSieve
