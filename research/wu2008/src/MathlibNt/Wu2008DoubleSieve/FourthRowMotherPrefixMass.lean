import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPairTriple
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherBandLabels

/-! # Exact Fubini transport of every coloured prefix label to actual source counts -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_tuple_length {P : Finset ℕ} {l : List ℕ} {r : ℕ}
    (hr : r = 2 ∨ r = 3 ∨ r = 4) (hl : l ∈ fourthRowMotherTuples P r) :
    l.length = r := by
  rcases hr with rfl | rfl | rfl
  · obtain ⟨p, _, rfl⟩ := mem_image.mp hl
    rfl
  · obtain ⟨p, _, rfl⟩ := mem_image.mp hl
    rfl
  · obtain ⟨p, _, rfl⟩ := mem_image.mp hl
    rfl

theorem fourthRowMother_prefix_in_tuples {P : Finset ℕ} {n r : ℕ} {l : List ℕ}
    (hr : r = 2 ∨ r = 3 ∨ r = 4)
    (hl : l ∈ fourthRowMotherPrefixes (divisorsIn P n) r) :
    l ∈ fourthRowMotherTuples P r := by
  have hlen := fourthRowMother_prefix_length hl
  rcases hr with rfl | rfl | rfl
  · obtain ⟨p, q, rfl⟩ := List.length_eq_two.mp hlen
    obtain ⟨hp, hq, hpq, _⟩ := fourthRowMother_mem_pair.mp hl
    exact fourthRowMother_tuple_pair.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hq).1, hpq⟩
  · obtain ⟨p, q, r, rfl⟩ := List.length_eq_three.mp hlen
    have ht := fourthRowMother_mem_triple.mp hl
    rw [firstTwoTriples_divisorsIn] at ht
    exact fourthRowMother_tuple_triple.mpr (mem_filter.mp ht).1
  · obtain ⟨p, q, r, t, rfl⟩ := List.length_eq_four.mp hlen
    obtain ⟨hp, hq, hr, ht, hpq, hqr, hrt, _⟩ := fourthRowMother_mem_quadruple.mp hl
    exact fourthRowMother_tuple_quadruple.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hq).1,
      (mem_filter.mp hr).1, (mem_filter.mp ht).1, hpq, hqr, hrt⟩

theorem fourthRowMother_tuple_carrier (N d : ℕ) {a f : ℝ} {l : List ℕ} {r : ℕ}
    (hr : r = 2 ∨ r = 3 ∨ r = 4)
    (hl : l ∈ fourthRowMotherTuples (primeWindow (d * N) a f) r) :
    (sieveCarrier N d (d * N) a).filter
      (fun ell => l ∈ fourthRowMotherPrefixes
        (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d)) r) =
      fourthRowMotherPrefixCarrier N d l := by
  have hlen := fourthRowMother_tuple_length hr hl
  rcases hr with rfl | rfl | rfl
  · obtain ⟨p, q, rfl⟩ := List.length_eq_two.mp hlen
    obtain ⟨hp, hq, hpq⟩ := fourthRowMother_tuple_pair.mp hl
    simpa [fourthRowMotherPrefixCarrier, mul_assoc] using
      fourthRowMother_pair_carrier N d hp hq hpq
  · obtain ⟨p, q, r, rfl⟩ := List.length_eq_three.mp hlen
    have ht := fourthRowMother_tuple_triple.mp hl
    simpa [fourthRowMotherPrefixCarrier, mul_assoc] using
      fourthRowMother_triple_carrier N d ht
  · obtain ⟨p, q, r, t, rfl⟩ := List.length_eq_four.mp hlen
    obtain ⟨hp, hq, hr, ht, hpq, hqr, hrt⟩ := fourthRowMother_tuple_quadruple.mp hl
    simpa [fourthRowMotherPrefixCarrier, mul_assoc] using
      fourthRowMother_quadruple_carrier N d hp hq hr ht hpq hqr hrt

theorem fourthRowMother_prefix_mass (N d : ℕ) (a b c f : ℝ) (cs : List ℕ)
    (hcs : cs.length = 2 ∨ cs.length = 3 ∨ cs.length = 4) :
    fourthRowMotherPrefixTerm N d (d * N) a b c f cs =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        ((fourthRowMotherColoured
          (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
          (fourthRowMotherColour b c) cs).card : ℝ) := by
  have hf (ell : ℕ) :
      fourthRowMotherColoured
        (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
        (fourthRowMotherColour b c) cs =
      (fourthRowMotherTuples (primeWindow (d * N) a f) cs.length).filter
        (fun l => l.map (fourthRowMotherColour b c) = cs ∧
          l ∈ fourthRowMotherPrefixes
            (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d)) cs.length) := by
    ext l
    simp only [fourthRowMotherColoured, mem_filter]
    constructor
    · rintro ⟨hl, hc⟩
      exact ⟨fourthRowMother_prefix_in_tuples hcs hl, hc, hl⟩
    · rintro ⟨_, hc, hl⟩
      exact ⟨hl, hc⟩
  simp only [fourthRowMotherPrefixTerm, hf, ← sum_boole]
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  rw [← fourthRowMother_tuple_carrier N d hcs hl]
  by_cases hc : l.map (fourthRowMotherColour b c) = cs
  · simp only [hc, if_true, true_and, sum_boole]
  · simp only [hc, if_false, false_and, sum_const_zero]

end Wu2008DoubleSieve
