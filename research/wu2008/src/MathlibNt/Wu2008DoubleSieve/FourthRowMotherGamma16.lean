import MathlibNt.Wu2008DoubleSieve.FourthRowMotherSourceBands

/-! # Lossless four-prefix transport to the accepted Gamma16 tuple carrier -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def fourthRowMotherVector (l : List ℕ) : Gamma16Tuple := fun j => l.getD j.val 0

theorem fourthRowMother_vector_list (p : Gamma16Tuple) :
    fourthRowMotherVector [p 0, p 1, p 2, p 3] = p := by
  funext j
  fin_cases j <;> rfl

theorem fourthRowMother_list_injective :
    Function.Injective (fun p : Gamma16Tuple => [p 0, p 1, p 2, p 3]) :=
  Function.LeftInverse.injective fourthRowMother_vector_list

theorem fourthRowMother_prefix_vector (N d : ℕ) {l : List ℕ} (hl : l.length = 4) :
    fourthRowMotherPrefixCarrier N d l = gamma16PrefixCarrier N d (fourthRowMotherVector l) := by
  obtain ⟨p, q, r, t, rfl⟩ := List.length_eq_four.mp hl
  simp [fourthRowMotherPrefixCarrier, gamma16PrefixCarrier, gamma16Product,
    fourthRowMotherVector, mul_assoc]

theorem fourthRowMother_prefix_output_bounds {N d ell : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hl : l.length = 4)
    (hell : ell ∈ fourthRowMotherPrefixCarrier N d l) :
    ∀ j, fourthRowMotherVector l j ≤ N := by
  rw [fourthRowMother_prefix_vector N d hl] at hell
  exact fourthRowMother_gamma16_output_bounds hN he hell

theorem fourthRowMother_gamma16_lists {N d : ℕ} {δ a b : ℝ}
    (hac : a ≤ wuLocalCutoff N δ d (291 / 100))
    (hbc : b ≤ wuLocalCutoff N δ d (291 / 100)) :
    ((fourthRowMotherTuples (primeWindow N a (wuLocalCutoff N δ d (5 / 2))) 4).filter
      (fun l => l.map (fourthRowMotherColour b (wuLocalCutoff N δ d (291 / 100))) = [2, 2, 2, 2])).filter
        (fun l => ∀ j, fourthRowMotherVector l j ≤ N) =
      (gamma16Tuples N δ d).image (fun p => [p 0, p 1, p 2, p 3]) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hl, hbound⟩ := mem_filter.mp hl
    obtain ⟨htuple, hcol⟩ := mem_filter.mp hl
    have hlen := fourthRowMother_tuple_length (Or.inr (Or.inr rfl)) htuple
    obtain ⟨p, q, r, t, rfl⟩ := List.length_eq_four.mp hlen
    obtain ⟨hp, hq, hr, ht, hpq, hqr, hrt⟩ := fourthRowMother_tuple_quadruple.mp htuple
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
      fourthRowMother_colour_two hbc] at hcol
    obtain ⟨hcp, hcq, hcr, hct⟩ := hcol
    refine mem_image.mpr ⟨fourthRowMotherVector [p, q, r, t], mem_gamma16Tuples.mpr ?_, rfl⟩
    refine ⟨?_, hpq, hqr, hrt, hbound⟩
    intro j
    fin_cases j
    · exact ⟨(mem_primeWindow.mp hp).1, (mem_primeWindow.mp hp).2.1,
        hcp, (mem_primeWindow.mp hp).2.2.2⟩
    · exact ⟨(mem_primeWindow.mp hq).1, (mem_primeWindow.mp hq).2.1,
        hcq, (mem_primeWindow.mp hq).2.2.2⟩
    · exact ⟨(mem_primeWindow.mp hr).1, (mem_primeWindow.mp hr).2.1,
        hcr, (mem_primeWindow.mp hr).2.2.2⟩
    · exact ⟨(mem_primeWindow.mp ht).1, (mem_primeWindow.mp ht).2.1,
        hct, (mem_primeWindow.mp ht).2.2.2⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hl
    obtain ⟨hall, h01, h12, h23, hbound⟩ := mem_gamma16Tuples.mp hp
    have hwin (j : Fin 4) : p j ∈ primeWindow N a (wuLocalCutoff N δ d (5 / 2)) :=
      mem_primeWindow.mpr ⟨(hall j).1, (hall j).2.1, hac.trans (hall j).2.2.1, (hall j).2.2.2⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨fourthRowMother_tuple_quadruple.mpr
      ⟨hwin 0, hwin 1, hwin 2, hwin 3, h01, h12, h23⟩, ?_⟩, ?_⟩
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
        fourthRowMother_colour_two hbc]
      exact ⟨(hall 0).2.2.1, (hall 1).2.2.1, (hall 2).2.2.1, (hall 3).2.2.1⟩
    · simpa only [fourthRowMother_vector_list] using hbound

theorem fourthRowMother_gamma16_mass {N d : ℕ} {δ a b : ℝ}
    (hN : 4 ≤ N) (he : Even N)
    (hac : a ≤ wuLocalCutoff N δ d (291 / 100))
    (hbc : b ≤ wuLocalCutoff N δ d (291 / 100)) :
    fourthRowMotherPrefixTerm N d N a b (wuLocalCutoff N δ d (291 / 100))
        (wuLocalCutoff N δ d (5 / 2)) [2, 2, 2, 2] =
      ∑ p ∈ gamma16Tuples N δ d,
        (sourceSieveCount N (d * gamma16Product p) (d * p 0 * p 1 * N) (p 2) : ℝ) := by
  let B := (fourthRowMotherTuples (primeWindow N a (wuLocalCutoff N δ d (5 / 2))) 4).filter
    (fun l => l.map (fourthRowMotherColour b (wuLocalCutoff N δ d (291 / 100))) = [2, 2, 2, 2])
  let A := B.filter (fun l => ∀ j, fourthRowMotherVector l j ≤ N)
  have hsum : (∑ l ∈ A, ((fourthRowMotherPrefixCarrier N d l).card : ℝ)) =
      ∑ l ∈ B, ((fourthRowMotherPrefixCarrier N d l).card : ℝ) := by
    apply sum_subset (filter_subset _ _)
    intro l hlB hlA
    apply Nat.cast_eq_zero.mpr
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro ell hell
    apply hlA
    have hlen := fourthRowMother_tuple_length (Or.inr (Or.inr rfl)) (mem_filter.mp hlB).1
    exact mem_filter.mpr ⟨hlB, fourthRowMother_prefix_output_bounds hN he hlen hell⟩
  have hset : A = (gamma16Tuples N δ d).image (fun p => [p 0, p 1, p 2, p 3]) :=
    fourthRowMother_gamma16_lists hac hbc
  change (∑ l ∈ fourthRowMotherTuples (primeWindow N a (wuLocalCutoff N δ d (5 / 2))) 4,
    if l.map (fourthRowMotherColour b (wuLocalCutoff N δ d (291 / 100))) = [2, 2, 2, 2]
      then ((fourthRowMotherPrefixCarrier N d l).card : ℝ) else 0) = _
  rw [← sum_filter]
  change (∑ l ∈ B, ((fourthRowMotherPrefixCarrier N d l).card : ℝ)) = _
  rw [← hsum, hset, sum_image (fun _ _ _ _ h => fourthRowMother_list_injective h)]
  apply sum_congr rfl
  intro p _
  rw [fourthRowMother_prefix_vector N d (by simp), fourthRowMother_vector_list]
  rfl

end Wu2008DoubleSieve
