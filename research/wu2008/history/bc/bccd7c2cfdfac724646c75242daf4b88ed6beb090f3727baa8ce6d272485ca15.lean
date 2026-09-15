import MathlibNt.Wu2008DoubleSieve.FourthRowMotherSourceBands

/-! # The whole surviving ninth triple term, separate from its overlapping addends -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_nine_ordered (N d M : ℕ) (b f : ℝ) :
    fourthRowMotherNine N d M b f =
      ∑ t ∈ orderedTriples (primeWindow M b f),
        (sourceSieveCount N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1 : ℝ) := by
  have h := sum_s3_orderedTriples_descending M b f
    (fun t => sourceSieveCount N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1)
  unfold fourthRowMotherNine
  exact_mod_cast h.symm

theorem fourthRowMother_nine_mass (N d : ℕ) (b f : ℝ) :
    fourthRowMotherNine N d (d * N) b f =
      ∑ ell ∈ sieveCarrier N d (d * N) b,
        (((divisorsIn (primeWindow (d * N) b f) ((N - ell) / d)).card - 2 : ℕ) : ℝ) := by
  have h : fourthRowMotherNine N d (d * N) b f =
      (tripleMass (sieveCarrier N d (d * N) b) (fun ell => (N - ell) / d)
        (primeWindow (d * N) b f) : ℝ) := by
    rw [fourthRowMother_nine_ordered, tripleMass_sieveCarrier, Int.cast_sum]
    apply sum_congr rfl
    intro t ht
    have ht' := ht
    simp only [orderedTriples, mem_filter, mem_product] at ht'
    obtain ⟨⟨_, hq, hr⟩, _, hqr⟩ := ht'
    simp only [sourceSieveCount, sieveCount, Int.cast_natCast]
    congr 2
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      omega_source_triple_carrier N d t.1 (mem_primeWindow.mp hq).1
        (mem_primeWindow.mp hr).1 hqr.le
  rw [h, tripleMass_eq_sum, Int.cast_sum]
  simp only [Int.cast_natCast, fourthRowMother_first_two_exact_card]

theorem fourthRowMother_nine_band_card (M n : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbf : b ≤ f) :
    ((fourthRowMotherColoured (divisorsIn (primeWindow M a f) n)
          (fourthRowMotherColour b c) [1, 1, 1]).card +
      (fourthRowMotherColoured (divisorsIn (primeWindow M a f) n)
          (fourthRowMotherColour b c) [1, 1, 2]).card +
      (fourthRowMotherColoured (divisorsIn (primeWindow M a f) n)
          (fourthRowMotherColour b c) [1, 2, 2]).card +
      (fourthRowMotherColoured (divisorsIn (primeWindow M a f) n)
          (fourthRowMotherColour b c) [2, 2, 2]).card) =
      if divisorsIn (primeWindow M a b) n = ∅
        then (divisorsIn (primeWindow M b f) n).card - 2 else 0 := by
  let s := divisorsIn (primeWindow M a f) n
  let χ := fourthRowMotherColour b c
  have hχ : Monotone χ := fourthRowMother_colour_monotone b c
  have hbnd : ∀ p ∈ s, χ p ≤ 2 := fun p _ => fourthRowMother_colour_le_two b c p
  change (fourthRowMotherColoured s χ [1, 1, 1]).card +
    (fourthRowMotherColoured s χ [1, 1, 2]).card +
    (fourthRowMotherColoured s χ [1, 2, 2]).card +
    (fourthRowMotherColoured s χ [2, 2, 2]).card = _
  simp only [fourthRowMother_coloured_card s χ hχ hbnd]
  rw [(fourthRowMother_band_formulas
    (fourthRowMotherColourCount s χ 0) (fourthRowMotherColourCount s χ 1)
    (fourthRowMotherColourCount s χ 2)).2.2.2.2.2.2.2]
  have hz : fourthRowMotherColourCount s χ 0 = 0 ↔
      divisorsIn (primeWindow M a b) n = ∅ := by
    rw [fourthRowMotherColourCount, fourthRowMother_band_zero M n hbf, card_eq_zero]
  have hc : fourthRowMotherColourCount s χ 1 + fourthRowMotherColourCount s χ 2 =
      (divisorsIn (primeWindow M b f) n).card := by
    have hall := fourthRowMother_colour_count_sum s χ hbnd
    have hs := sum_filter_add_sum_filter_not s (fun p => χ p = 0) (fun _ => (1 : ℕ))
    simp only [sum_const, smul_eq_mul, mul_one] at hs
    rw [show s.filter (fun p => ¬χ p = 0) = divisorsIn (primeWindow M b f) n from
      fourthRowMother_band_high M n hab] at hs
    change fourthRowMotherColourCount s χ 0 +
      (divisorsIn (primeWindow M b f) n).card = s.card at hs
    omega
  simp only [hz, hc]

theorem fourthRowMother_gamma9_mass (N d : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbf : b ≤ f) :
    fourthRowMotherNine N d (d * N) b f =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        (((fourthRowMotherColoured (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
              (fourthRowMotherColour b c) [1, 1, 1]).card +
          (fourthRowMotherColoured (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
              (fourthRowMotherColour b c) [1, 1, 2]).card +
          (fourthRowMotherColoured (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
              (fourthRowMotherColour b c) [1, 2, 2]).card +
          (fourthRowMotherColoured (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
              (fourthRowMotherColour b c) [2, 2, 2]).card : ℕ) : ℝ) := by
  rw [fourthRowMother_nine_mass, ← siftedIndices_sieveCarrier N d (d * N) hab]
  simp only [siftedIndices, sum_filter, fourthRowMother_nine_band_card _ _ hab hbf,
    Nat.cast_ite, Nat.cast_zero]

end Wu2008DoubleSieve
