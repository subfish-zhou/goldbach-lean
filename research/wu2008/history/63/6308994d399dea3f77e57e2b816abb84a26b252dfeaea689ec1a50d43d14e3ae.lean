import R2RawMotherWitness

namespace WuPaper.R2RawMother

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def floorGamma (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) : ℝ :=
  if j < 7 then 0
  else ((secondFunctionalMotherGammaWords j).map (exceptionFloorTerm N d M a b c e f)).sum

noncomputable def floorWeighted (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ j ∈ Icc 5 21, floorGamma N d N
      (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
      (wuLocalCutoff N δ d p.s) j

theorem exceptionWeighted_le_floor (p : SecondFunctionalParameters)
    {i N : ℕ} (δ : ℝ) (W : Fin i → Finset ℕ) (hN : 4 ≤ N) (he : Even N) :
    exceptionWeighted p N δ W ≤ floorWeighted p N δ W := by
  unfold exceptionWeighted floorWeighted exceptionLocal
  apply sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro j _
  unfold exceptionGamma floorGamma
  split_ifs
  · rfl
  · exact secondFunctionalMother_list_sum_mono _ _ _
      (fun cs _ => exceptionTerm_floor _ _ _ _ _ _ _ cs hN he)

theorem raw_source_finite_floor
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
      rawWeighted p N δ (convolutionWuWindows N Δ V) +
        floorWeighted p N δ (convolutionWuWindows N Δ V) +
          secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) :=
  (raw_source_finite_with_exception p hp (by omega) hδ hδhi hb).trans
    (add_le_add (add_le_add le_rfl (exceptionWeighted_le_floor p δ _ hN he)) le_rfl)

theorem prime_word_witness (l : List ℕ) {s t : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hst : s ≤ t) (hord : (l ++ [s, t]).Pairwise (· < ·))
    (hp : ∀ q ∈ l ++ [s, t], q.Prime)
    (hlarge : ∀ q ∈ l ++ [s, t], 3 < q)
    (hbounds : ∀ q ∈ l ++ [s, t], a ≤ (q : ℝ) ∧ (q : ℝ) < f)
    (hc : (l ++ [s, t]).map (secondFunctionalMotherColour b c e) = cs) :
    1 ≤ secondFunctionalMotherPrefixTerm ((l ++ [s, t]).prod + 3) 1
      ((l ++ [s, t]).prod + 3) a b c e f cs := by
  refine prefixTerm_one_le_of_witness (l := l ++ [s, t]) (ell := 3) ?_ hc ?_
  · apply (secondFunctionalMother_tuple_mem _ _ _).mpr
    refine ⟨?_, hord, ?_⟩
    · simpa only [List.length_map] using congrArg List.length hc
    · intro q hq
      exact mem_primeWindow.mpr ⟨hp q hq,
        prime_list_product_add_three_coprime _ (hp q hq) hq (hlarge q hq), hbounds q hq⟩
  · exact prefix_suffix_witness l (hp s (by simp)) (hp t (by simp)) hst

theorem colour_two_nat {b c e v : ℕ} (hb : b ≤ v) (hc : c ≤ v) (he : v < e) :
    secondFunctionalMotherColour b c e v = 2 := by
  unfold secondFunctionalMotherColour
  rw [if_neg (not_lt.mpr (by exact_mod_cast hb)),
    if_neg (not_lt.mpr (by exact_mod_cast hc)), if_pos (by exact_mod_cast he)]

theorem colour_three_nat {b c e v : ℕ} (hb : b ≤ v) (hc : c ≤ v) (he : e ≤ v) :
    secondFunctionalMotherColour b c e v = 3 := by
  unfold secondFunctionalMotherColour
  rw [if_neg (not_lt.mpr (by exact_mod_cast hb)),
    if_neg (not_lt.mpr (by exact_mod_cast hc)), if_neg (not_lt.mpr (by exact_mod_cast he))]

theorem gamma20_squarefree_discrepancy {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hp3 : 3 < p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) :
    let N := [p, q, r, s, t].prod + 3
    Even N ∧ Squarefree (N - 3) ∧
      rawGamma N 1 N 2 3 p q (t + 1) 20 = 0 ∧
        1 ≤ exceptionGamma N 1 N 2 3 p q (t + 1) 20 := by
  dsimp only
  have hord : [p, q, r, s, t].Pairwise (· < ·) := by simp; omega
  have hprime : ∀ v ∈ [p, q, r, s, t], v.Prime := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hlarge : ∀ v ∈ [p, q, r, s, t], 3 < v := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    omega
  refine ⟨prime_list_product_add_three_even _ hprime hlarge, ?_,
    rawGamma20_unit_zero _ _ _ _ _ _, ?_⟩
  · simpa only [Nat.add_sub_cancel] using ordered_prime_prod_squarefree _ hord hprime
  · rw [exceptionGamma20_unit_full]
    simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    apply prime_word_witness [p, q, r] hst.le hord hprime hlarge
    · intro v hv
      have hv3 := hlarge v hv
      have hvt : v ≤ t := by
        change v ∈ [p, q, r, s, t] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
      constructor
      · exact_mod_cast (by omega : 2 ≤ v)
      · exact_mod_cast (by omega : v < t + 1)
    · change [p, q, r, s, t].map (secondFunctionalMotherColour 3 p q) = [2, 3, 3, 3, 3]
      have hc3 (v : ℕ) (hqv : q ≤ v) :
          secondFunctionalMotherColour 3 p q v = 3 :=
        colour_three_nat (by omega : 3 ≤ v) (by omega) hqv
      simp only [List.map_cons, List.map_nil,
        colour_two_nat hp3.le le_rfl hpq,
        hc3 q le_rfl, hc3 r hqr.le, hc3 s (by omega), hc3 t (by omega)]

theorem gamma21_squarefree_discrepancy {p q r s t u : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (ht : t.Prime) (hu : u.Prime)
    (hp3 : 3 < p) (hpq : p < q) (hqr : q < r)
    (hrs : r < s) (hst : s < t) (htu : t < u) :
    let N := [p, q, r, s, t, u].prod + 3
    Even N ∧ Squarefree (N - 3) ∧
      rawGamma N 1 N 2 3 4 p (u + 1) 21 = 0 ∧
        1 ≤ exceptionGamma N 1 N 2 3 4 p (u + 1) 21 := by
  dsimp only
  have hord : [p, q, r, s, t, u].Pairwise (· < ·) := by simp; omega
  have hprime : ∀ v ∈ [p, q, r, s, t, u], v.Prime := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hlarge : ∀ v ∈ [p, q, r, s, t, u], 3 < v := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    omega
  refine ⟨prime_list_product_add_three_even _ hprime hlarge, ?_,
    rawGamma21_unit_zero _ _ _ _ _ _, ?_⟩
  · simpa only [Nat.add_sub_cancel] using ordered_prime_prod_squarefree _ hord hprime
  · rw [exceptionGamma21_unit_full]
    simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    apply prime_word_witness [p, q, r, s] htu.le hord hprime hlarge
    · intro v hv
      have hv3 := hlarge v hv
      have hvu : v ≤ u := by
        change v ∈ [p, q, r, s, t, u] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
      constructor
      · exact_mod_cast (by omega : 2 ≤ v)
      · exact_mod_cast (by omega : v < u + 1)
    · change [p, q, r, s, t, u].map (secondFunctionalMotherColour 3 4 p) =
        [3, 3, 3, 3, 3, 3]
      have hc3 (v : ℕ) (hpv : p ≤ v) :
          secondFunctionalMotherColour 3 4 p v = 3 :=
        colour_three_nat (by omega : 3 ≤ v) (by omega : 4 ≤ v) hpv
      simp only [List.map_cons, List.map_nil,
        hc3 p le_rfl, hc3 q hpq.le, hc3 r (by omega), hc3 s (by omega),
        hc3 t (by omega), hc3 u (by omega)]

end WuPaper.R2RawMother

#check @WuPaper.R2RawMother.floorGamma
#print axioms WuPaper.R2RawMother.floorGamma
#check @WuPaper.R2RawMother.floorWeighted
#print axioms WuPaper.R2RawMother.floorWeighted
#check @WuPaper.R2RawMother.exceptionWeighted_le_floor
#print axioms WuPaper.R2RawMother.exceptionWeighted_le_floor
#check @WuPaper.R2RawMother.raw_source_finite_floor
#print axioms WuPaper.R2RawMother.raw_source_finite_floor
#check @WuPaper.R2RawMother.prime_word_witness
#print axioms WuPaper.R2RawMother.prime_word_witness
#check @WuPaper.R2RawMother.colour_two_nat
#print axioms WuPaper.R2RawMother.colour_two_nat
#check @WuPaper.R2RawMother.colour_three_nat
#print axioms WuPaper.R2RawMother.colour_three_nat
#check @WuPaper.R2RawMother.gamma20_squarefree_discrepancy
#print axioms WuPaper.R2RawMother.gamma20_squarefree_discrepancy
#check @WuPaper.R2RawMother.gamma21_squarefree_discrepancy
#print axioms WuPaper.R2RawMother.gamma21_squarefree_discrepancy

#check @WuPaper.R2RawMother.source_modulus_dichotomy
#print axioms WuPaper.R2RawMother.source_modulus_dichotomy
#check @WuPaper.R2RawMother.rawCarrier
#print axioms WuPaper.R2RawMother.rawCarrier
#check @WuPaper.R2RawMother.labelsSurvive
#print axioms WuPaper.R2RawMother.labelsSurvive
#check @WuPaper.R2RawMother.exceptionalCarrier
#print axioms WuPaper.R2RawMother.exceptionalCarrier
#check @WuPaper.R2RawMother.rawCarrier_dichotomy
#print axioms WuPaper.R2RawMother.rawCarrier_dichotomy
#check @WuPaper.R2RawMother.prefix_card_exact
#print axioms WuPaper.R2RawMother.prefix_card_exact
#check @WuPaper.R2RawMother.rawCarrier_empty_of_selected
#print axioms WuPaper.R2RawMother.rawCarrier_empty_of_selected
#check @WuPaper.R2RawMother.exceptional_eq_prefix_of_selected
#print axioms WuPaper.R2RawMother.exceptional_eq_prefix_of_selected
#check @WuPaper.R2RawMother.raw_five_empty
#print axioms WuPaper.R2RawMother.raw_five_empty
#check @WuPaper.R2RawMother.raw_six_empty
#print axioms WuPaper.R2RawMother.raw_six_empty
#check @WuPaper.R2RawMother.exceptional_card_floor
#print axioms WuPaper.R2RawMother.exceptional_card_floor
#check @WuPaper.R2RawMother.sifted_prime_iff
#print axioms WuPaper.R2RawMother.sifted_prime_iff
#check @WuPaper.R2RawMother.labelsSurvive_five_iff
#print axioms WuPaper.R2RawMother.labelsSurvive_five_iff
#check @WuPaper.R2RawMother.labelsSurvive_six_iff
#print axioms WuPaper.R2RawMother.labelsSurvive_six_iff
#check @WuPaper.R2RawMother.rawTerm
#print axioms WuPaper.R2RawMother.rawTerm
#check @WuPaper.R2RawMother.exceptionTerm
#print axioms WuPaper.R2RawMother.exceptionTerm
#check @WuPaper.R2RawMother.term_exact
#print axioms WuPaper.R2RawMother.term_exact
#check @WuPaper.R2RawMother.ordered_raw_empty
#print axioms WuPaper.R2RawMother.ordered_raw_empty
#check @WuPaper.R2RawMother.rawTerm_masked_zero
#print axioms WuPaper.R2RawMother.rawTerm_masked_zero
#check @WuPaper.R2RawMother.rawTerm_unit_zero
#print axioms WuPaper.R2RawMother.rawTerm_unit_zero
#check @WuPaper.R2RawMother.exceptionTerm_unit_eq_prefix
#print axioms WuPaper.R2RawMother.exceptionTerm_unit_eq_prefix
#check @WuPaper.R2RawMother.rawGamma
#print axioms WuPaper.R2RawMother.rawGamma
#check @WuPaper.R2RawMother.exceptionGamma
#print axioms WuPaper.R2RawMother.exceptionGamma
#check @WuPaper.R2RawMother.words_exact
#print axioms WuPaper.R2RawMother.words_exact
#check @WuPaper.R2RawMother.gamma_exact
#print axioms WuPaper.R2RawMother.gamma_exact
#check @WuPaper.R2RawMother.rawLocal
#print axioms WuPaper.R2RawMother.rawLocal
#check @WuPaper.R2RawMother.exceptionLocal
#print axioms WuPaper.R2RawMother.exceptionLocal
#check @WuPaper.R2RawMother.local_exact
#print axioms WuPaper.R2RawMother.local_exact
#check @WuPaper.R2RawMother.raw_local_with_exact_exception
#print axioms WuPaper.R2RawMother.raw_local_with_exact_exception
#check @WuPaper.R2RawMother.exceptionFloorTerm
#print axioms WuPaper.R2RawMother.exceptionFloorTerm
#check @WuPaper.R2RawMother.exceptionTerm_floor
#print axioms WuPaper.R2RawMother.exceptionTerm_floor
#check @WuPaper.R2RawMother.rawWeighted
#print axioms WuPaper.R2RawMother.rawWeighted
#check @WuPaper.R2RawMother.exceptionWeighted
#print axioms WuPaper.R2RawMother.exceptionWeighted
#check @WuPaper.R2RawMother.weighted_exact
#print axioms WuPaper.R2RawMother.weighted_exact
#check @WuPaper.R2RawMother.raw_source_finite_with_exception
#print axioms WuPaper.R2RawMother.raw_source_finite_with_exception
#check @WuPaper.R2RawMother.raw_source_with_exception
#print axioms WuPaper.R2RawMother.raw_source_with_exception
#check @WuPaper.R2RawMother.rawGamma20_unit_zero
#print axioms WuPaper.R2RawMother.rawGamma20_unit_zero
#check @WuPaper.R2RawMother.rawGamma21_unit_zero
#print axioms WuPaper.R2RawMother.rawGamma21_unit_zero
#check @WuPaper.R2RawMother.exceptionGamma20_unit_full
#print axioms WuPaper.R2RawMother.exceptionGamma20_unit_full
#check @WuPaper.R2RawMother.exceptionGamma21_unit_full
#print axioms WuPaper.R2RawMother.exceptionGamma21_unit_full
#check @WuPaper.R2RawMother.ordered_prime_prod_squarefree
#print axioms WuPaper.R2RawMother.ordered_prime_prod_squarefree
#check @WuPaper.R2RawMother.prime_list_product_add_three_coprime
#print axioms WuPaper.R2RawMother.prime_list_product_add_three_coprime
#check @WuPaper.R2RawMother.prime_list_product_add_three_even
#print axioms WuPaper.R2RawMother.prime_list_product_add_three_even
#check @WuPaper.R2RawMother.prefix_suffix_carrier
#print axioms WuPaper.R2RawMother.prefix_suffix_carrier
#check @WuPaper.R2RawMother.prefix_suffix_witness
#print axioms WuPaper.R2RawMother.prefix_suffix_witness
#check @WuPaper.R2RawMother.squarefree_exception_witness
#print axioms WuPaper.R2RawMother.squarefree_exception_witness
#check @WuPaper.R2RawMother.prefixTerm_one_le_of_witness
#print axioms WuPaper.R2RawMother.prefixTerm_one_le_of_witness
