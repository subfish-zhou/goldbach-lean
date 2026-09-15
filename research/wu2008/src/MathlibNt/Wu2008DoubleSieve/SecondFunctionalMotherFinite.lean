import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSourceBands

/-! # The finite masked four-band source inequality -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

theorem secondFunctionalMother_prefix_lengths (i : ℕ)
    (hi : i ∈ secondFunctionalMotherPrefixIndices) (cs : List ℕ)
    (hcs : cs ∈ secondFunctionalMotherGammaWords i) : 2 ≤ cs.length := by
  simp only [secondFunctionalMotherPrefixIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [secondFunctionalMotherGammaWords, List.mem_cons, List.not_mem_nil, or_false] at hcs <;>
    aesop

theorem secondFunctionalMother_local_expand (N d M : ℕ) (a b c e f : ℝ) :
    secondFunctionalMotherLocal N d M a b c e f =
      4 * (sourceSieveCount N d (d*N) a : ℝ) + (sourceSieveCount N d (d*N) b : ℝ) -
      fourthRowMotherSingle N d M a f - fourthRowMotherSingle N d M a c -
      fourthRowMotherSingle N d M a e + fourthRowMotherPair N d M a c a c +
      fourthRowMotherPair N d M a b c e +
      (secondFunctionalMotherPrefixIndices.map fun i =>
        ((secondFunctionalMotherGammaWords i).map
          (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum).sum := by
  norm_num [secondFunctionalMotherLocal, secondFunctionalMotherGamma,
    secondFunctionalMotherPrefixIndices, secondFunctionalMotherGammaWords, sum_Icc_succ_top]
  ring

theorem secondFunctionalMother_words_mass_le (N d : ℕ) (a b c e f : ℝ)
    (css : List (List ℕ)) (hcss : ∀ cs ∈ css, 2 ≤ cs.length) :
    (∑ ell ∈ sieveCarrier N d (d*N) a,
      (((css.map fun cs => (fourthRowMotherColoured
        (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
        (secondFunctionalMotherColour b c e) cs).card).sum : ℕ) : ℝ)) ≤
      (css.map (secondFunctionalMotherPrefixTerm N d (d*N) a b c e f)).sum := by
  induction css with
  | nil => simp
  | cons cs css ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, sum_add_distrib]
      exact add_le_add (secondFunctionalMother_prefix_mass_le N d a b c e f cs
        (hcss cs (by simp))) (ih (fun t ht => hcss t (by simp [ht])))

theorem secondFunctionalMother_package_mass_le (N d : ℕ) (a b c e f : ℝ)
    (is : List ℕ) (his : ∀ i ∈ is, ∀ cs ∈ secondFunctionalMotherGammaWords i, 2 ≤ cs.length) :
    (∑ ell ∈ sieveCarrier N d (d*N) a,
      (is.map fun i => (secondFunctionalMotherGammaLabels
        (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
        (secondFunctionalMotherColour b c e) i : ℝ)).sum) ≤
      (is.map fun i => ((secondFunctionalMotherGammaWords i).map
        (secondFunctionalMotherPrefixTerm N d (d*N) a b c e f)).sum).sum := by
  induction is with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons, sum_add_distrib]
      exact add_le_add (secondFunctionalMother_words_mass_le N d a b c e f _
        (his i (by simp))) (ih (fun j hj => his j (by simp [hj])))

theorem secondFunctionalMother_masked (N d : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    5 * (sourceSieveCount N d (d*N) f : ℝ) ≤ secondFunctionalMotherLocal N d (d*N) a b c e f := by
  have hw := secondFunctionalMother_actual_weight_sum (N := N) (d := d)
    (b := b) (c := c) (e := e) (hab.trans (hbc.trans (hce.trans hef)))
  have hp := secondFunctionalMother_package_mass_le N d a b c e f
    secondFunctionalMotherPrefixIndices secondFunctionalMother_prefix_lengths
  rw [secondFunctionalMother_local_expand,
    fourthRowMother_single_mass, fourthRowMother_single_mass, fourthRowMother_single_mass,
    secondFunctionalMother_gamma5_mass N d hbc (hce.trans hef),
    secondFunctionalMother_gamma6_mass N d hab hbc hce hef,
    fourthRowMother_cutoff_card N d hab]
  simp only [secondFunctionalMotherLabelWeight,
    secondFunctionalMother_band_zero _ _ (hbc.trans (hce.trans hef)),
    secondFunctionalMother_band_low _ _ hbc (hce.trans hef),
    secondFunctionalMother_band_mid _ _ hbc hce hef,
    sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul] at hw
  simp only [sourceSieveCount, source_double_sieve_carriers, Int.cast_natCast] at hw ⊢
  linarith

end Wu2008DoubleSieve
