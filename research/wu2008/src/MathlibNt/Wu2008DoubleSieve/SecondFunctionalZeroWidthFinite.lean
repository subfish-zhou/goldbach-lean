import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunit

/-! Zero-width elimination on the original strict prime window and full labels.
No closed-envelope endpoint is asserted empty. -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

namespace SecondFunctionalZeroWidth

theorem colour_ne_three {M q : ℕ} {a b c f : ℝ}
    (hq : q ∈ primeWindow M a f) : secondFunctionalMotherColour b c f q ≠ 3 := by
  have hqf := (mem_primeWindow.mp hq).2.2.2
  unfold secondFunctionalMotherColour
  simp only [hqf, if_true]
  split_ifs <;> omega

/-- Any full word containing colour three has no original ordered label. -/
theorem word_ne {M : ℕ} {a b c f : ℝ} {cs l : List ℕ}
    (hcs : 3 ∈ cs) (hl : l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length) :
    l.map (secondFunctionalMotherColour b c f) ≠ cs := by
  intro heq
  have hm : 3 ∈ l.map (secondFunctionalMotherColour b c f) := heq.symm ▸ hcs
  obtain ⟨q,hq,hcol⟩ := List.mem_map.mp hm
  exact colour_ne_three (((secondFunctionalMother_tuple_mem _ _ _).mp hl).2.2 q hq) hcol

theorem label_filter_empty (M : ℕ) (a b c f : ℝ) (cs : List ℕ) (hcs : 3 ∈ cs) :
    ((secondFunctionalMotherTuples (primeWindow M a f) cs.length).filter
      fun l => l.map (secondFunctionalMotherColour b c f) = cs) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro l hl
  exact word_ne hcs (mem_filter.mp hl).1 (mem_filter.mp hl).2

theorem prefix_zero (N d M : ℕ) (a b c f : ℝ) (cs : List ℕ) (hcs : 3 ∈ cs) :
    secondFunctionalMotherPrefixTerm N d M a b c f f cs = 0 := by
  apply sum_eq_zero
  intro l hl
  exact if_neg (word_ne hcs hl)

theorem masked_prefix_zero (unit : Bool) (N d : ℕ) (a b c f : ℝ)
    (cs : List ℕ) (hcs : 3 ∈ cs) : FourPrimeUnit.prefixTerm unit N d a b c f f cs = 0 := by
  apply sum_eq_zero
  intro l hl
  exact if_neg (word_ne hcs hl)

theorem gamma_zero (N d M : ℕ) (a b c f : ℝ) {j : ℕ}
    (hj : j = 12 ∨ j = 15 ∨ j = 20 ∨ j = 21) :
    secondFunctionalMotherGamma N d M a b c f f j = 0 := by
  rcases hj with rfl | rfl | rfl | rfl <;>
    simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] <;>
    apply prefix_zero <;> simp

theorem gamma_sum_zero (p : SecondFunctionalParameters) (he : p.kappa3 = p.s)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) {j : ℕ}
    (hj : j = 12 ∨ j = 15 ∨ j = 20 ∨ j = 21) :
    secondFunctionalMotherGammaSum p N δ W j = 0 := by
  unfold secondFunctionalMotherGammaSum
  apply sum_eq_zero
  intro d _
  rw [he, gamma_zero N d N _ _ _ _ hj, mul_zero]

/-- Neither a residual-quotient mask nor a unit/nonunit split can restore an absent label. -/
theorem nonunit_sum_zero (p : SecondFunctionalParameters) (he : p.kappa3 = p.s)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) {j : Fin 4} (hj : j ≠ 0) :
    secondFunctionalFourPrimeNonunitSum p N δ W j = 0 := by
  have hword : 3 ∈ FourPrimeUnit.word j := by
    fin_cases j <;> simp_all [FourPrimeUnit.word]
  unfold secondFunctionalFourPrimeNonunitSum
  apply sum_eq_zero
  intro d _
  rw [he, masked_prefix_zero false N d _ _ _ _ _ hword, mul_zero]

theorem actual_nonunit_source_zero (p : SecondFunctionalParameters) (he : p.kappa3 = p.s)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) {j : Fin 4} (hj : j ≠ 0) :
    FourPrimeNonunit.actualSource N δ p W j = 0 := by
  rw [FourPrimeNonunit.actual_source_eq]
  exact nonunit_sum_zero p he N δ W hj

/-- Explicit retained original counts. In particular multiword Gamma10/13/14 remain. -/
noncomputable def retained (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  secondFunctionalMotherGammaSum p N δ W 5 +
  secondFunctionalMotherGammaSum p N δ W 6 +
  secondFunctionalMotherGammaSum p N δ W 7 +
  secondFunctionalMotherGammaSum p N δ W 8 +
  secondFunctionalMotherGammaSum p N δ W 9 +
  secondFunctionalMotherGammaSum p N δ W 10 +
  secondFunctionalMotherGammaSum p N δ W 11 +
  secondFunctionalMotherGammaSum p N δ W 13 +
  secondFunctionalMotherGammaSum p N δ W 14

theorem retained_eq (p : SecondFunctionalParameters) (he : p.kappa3 = p.s)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ W j) = retained p N δ W := by
  have h12 := gamma_sum_zero p he N δ W (j := 12) (Or.inl rfl)
  have h15 := gamma_sum_zero p he N δ W (j := 15) (Or.inr (Or.inl rfl))
  rw [sum_Icc_succ_top (a := 5) (b := 14) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 13) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 12) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 11) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 10) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 9) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 8) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 7) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 6) (by omega)]
  rw [sum_Icc_succ_top (a := 5) (b := 5) (by omega)]
  simp only [Icc_self, sum_singleton, h12, h15, add_zero, retained]

theorem ledger_eq (p : SecondFunctionalParameters) (he : p.kappa3 = p.s)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    secondFunctionalNonunitGammaLedger p N δ W =
      retained p N δ W + secondFunctionalFourPrimeNonunitSum p N δ W 0 := by
  have h20 := gamma_sum_zero p he N δ W (j := 20) (Or.inr (Or.inr (Or.inl rfl)))
  have h21 := gamma_sum_zero p he N δ W (j := 21) (Or.inr (Or.inr (Or.inr rfl)))
  have h1 := nonunit_sum_zero p he N δ W (j := 1) (by decide)
  have h2 := nonunit_sum_zero p he N δ W (j := 2) (by decide)
  have h3 := nonunit_sum_zero p he N δ W (j := 3) (by decide)
  simp [secondFunctionalNonunitGammaLedger, retained_eq p he, Fin.sum_univ_succ,
    h1, h2, h3, h20, h21]

end SecondFunctionalZeroWidth
end Wu2008DoubleSieve
