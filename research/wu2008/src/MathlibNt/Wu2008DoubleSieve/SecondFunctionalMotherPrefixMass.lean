import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPrefixBridge
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherLabels

/-! # Fubini transport to genuine prefix source counts, for arbitrary arity -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

theorem secondFunctionalMother_prefix_mass_le (N d : ℕ) (a b c e f : ℝ)
    (cs : List ℕ) (hcs : 2 ≤ cs.length) :
    (∑ ell ∈ sieveCarrier N d (d*N) a,
      ((fourthRowMotherColoured
        (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
        (secondFunctionalMotherColour b c e) cs).card : ℝ)) ≤
      secondFunctionalMotherPrefixTerm N d (d*N) a b c e f cs := by
  let P := primeWindow (d*N) a f
  let A := sieveCarrier N d (d*N) a
  let χ := secondFunctionalMotherColour b c e
  have hf (ell : ℕ) :
      fourthRowMotherColoured (divisorsIn P ((N-ell)/d)) χ cs =
      (secondFunctionalMotherTuples P cs.length).filter
        (fun l => l.map χ = cs ∧
          l ∈ fourthRowMotherPrefixes (divisorsIn P ((N-ell)/d)) cs.length) := by
    ext l
    simp only [fourthRowMotherColoured, mem_filter]
    constructor
    · rintro ⟨hl, hc⟩
      exact ⟨secondFunctionalMother_prefix_in_tuples hl, hc, hl⟩
    · rintro ⟨_, hc, hl⟩
      exact ⟨hl, hc⟩
  have he : (∑ ell ∈ A, ((fourthRowMotherColoured (divisorsIn P ((N-ell)/d)) χ cs).card : ℝ)) =
      ∑ l ∈ secondFunctionalMotherTuples P cs.length,
        if l.map χ = cs then ((A.filter fun ell =>
          l ∈ fourthRowMotherPrefixes (divisorsIn P ((N-ell)/d)) cs.length).card : ℝ) else 0 := by
    simp only [hf, ← sum_boole]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    by_cases hc : l.map χ = cs
    · simp only [hc, if_true, true_and]
    · simp only [hc, if_false, false_and, sum_const_zero]
  change (∑ ell ∈ A, ((fourthRowMotherColoured (divisorsIn P ((N-ell)/d)) χ cs).card : ℝ)) ≤ _
  rw [he]
  apply sum_le_sum
  intro l hl
  have hlen := ((secondFunctionalMother_tuple_mem P cs.length l).mp hl).1
  dsimp only [χ]
  by_cases hc : l.map (secondFunctionalMotherColour b c e) = cs
  · simp only [if_pos hc]
    have hsub := secondFunctionalMother_prefix_source_subset N d
      (a := a) (f := f) (l := l) (by omega)
    rw [hlen] at hsub
    exact_mod_cast card_le_card hsub
  · simp only [if_neg hc, le_refl]

theorem secondFunctionalMother_actual_weight_sum (N d : ℕ) {a b c e f : ℝ}
    (haf : a ≤ f) :
    5 * (sourceSieveCount N d (d*N) f : ℝ) ≤
      ∑ ell ∈ sieveCarrier N d (d*N) a,
        secondFunctionalMotherLabelWeight
          (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
          (secondFunctionalMotherColour b c e) := by
  rw [fourthRowMother_cutoff_card N d haf, mul_sum]
  apply sum_le_sum
  intro ell _
  simpa only [mul_ite, mul_one, mul_zero] using
    secondFunctionalMother_label_weight
      (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
      (secondFunctionalMotherColour b c e)
      (secondFunctionalMother_colour_monotone b c e)
      (fun p _ => secondFunctionalMother_colour_le_three b c e p)

end Wu2008DoubleSieve
