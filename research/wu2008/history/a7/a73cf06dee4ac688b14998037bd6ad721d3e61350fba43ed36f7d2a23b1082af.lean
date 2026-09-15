import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateProfiles

/-! # Actual no-gate prefix counts, with every switching exception paid -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem fourthRowTripleNoGate_switched_reorder {i : ℕ} (N : ℕ) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) :
    (omega3LabelSum N δ (5 / 2) (103 / 25) W fun d p q r =>
      if fourthRowTripleNoGateBand N δ eleven d p q then
        ((omega3SiftedSwitchedFibre N d p q r Z).card : ℝ) else 0) =
      ∑ c ∈ fourthRowTripleNoGateProfiles N δ W eleven, (convolutionCoeff W c.1 : ℝ) *
        (((omega3CofactorPrimeFibre N δ (5 / 2) c).filter
          (fun p => Sifted N (N - omega3CofactorValue c * p) Z)).card : ℝ) := by
  let test : Omega3Index → ℝ := fun a =>
    if fourthRowTripleNoGateBand N δ eleven a.1 a.2.2.2.1 a.2.2.1 ∧
      Sifted N (omega3IndexOutput N a) Z then 1 else 0
  have h := (omega3_switched_labels_sum N δ (5 / 2) (103 / 25) W test).symm.trans
    (omega3_cofactor_first_sum N δ (5 / 2) (103 / 25) W test)
  have hs (d p q r : ℕ) :
      (∑ n ∈ omega3SwitchedFibre N d p q r, test ⟨d, r, q, p, n⟩) =
        if fourthRowTripleNoGateBand N δ eleven d p q then
          ((omega3SiftedSwitchedFibre N d p q r Z).card : ℝ) else 0 := by
    by_cases hb : fourthRowTripleNoGateBand N δ eleven d p q
    · simp only [test, hb, true_and, if_true, omega3SiftedSwitchedFibre,
        omega3IndexOutput, omega3IndexCofactor, ← sum_boole]
    · simp only [test, hb, false_and, if_false, sum_const_zero]
  simp only [hs] at h
  rw [h]
  simp only [fourthRowTripleNoGateProfiles, sum_filter, test,
    omega3RestorePrime, omega3IndexOutput, omega3IndexCofactor, omega3CofactorValue]
  apply sum_congr rfl
  intro c _
  by_cases hb : fourthRowTripleNoGateBand N δ eleven c.1 c.2.2.1 c.2.1
  · simp only [hb, true_and, if_true, sum_boole]
    rfl
  · simp only [hb, false_and, if_false, sum_const_zero, mul_zero]

theorem fourthRowTripleNoGate_switching_finite {i N : ℕ} {δ : ℝ}
    (W : Fin i → Finset ℕ) (eleven : Bool) (hN : 4 ≤ N) (he : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    fourthRowMotherPrefixSum N δ W (fourthRowTripleNoGateWord eleven) ≤
      fourthRowTripleNoGateS N δ (sqrt ((N : ℝ) ^ (1 / 2 - δ))) W eleven +
        omega3BadDCount N δ (5 / 2) (103 / 25) W +
        omega3ExceptionalOutputCount N δ (5 / 2) (103 / 25) W := by
  let Z := sqrt ((N : ℝ) ^ (1 / 2 - δ))
  have hfinite :
      fourthRowMotherPrefixSum N δ W (fourthRowTripleNoGateWord eleven) ≤
        (omega3LabelSum N δ (5 / 2) (103 / 25) W fun d p q r =>
          if fourthRowTripleNoGateBand N δ eleven d p q then
            ((omega3SiftedSwitchedFibre N d p q r Z).card : ℝ) else 0) +
        omega3BadDCount N δ (5 / 2) (103 / 25) W +
        omega3ExceptionalOutputCount N δ (5 / 2) (103 / 25) W := by
    rw [fourthRowTripleNoGate_original_sum]
    unfold omega3BadDCount omega3ExceptionalOutputCount
    rw [← omega3LabelSum_add, ← omega3LabelSum_add]
    apply omega3LabelSum_mono
    intro d hd' r _ q hq p hp
    by_cases hb : fourthRowTripleNoGateBand N δ eleven d p q
    · simp only [hb, if_true]
      exact_mod_cast omega3_fibre_switching_exceptional_bound (p3 := r) (δ := δ)
        hN he (hd d hd') (mem_primeWindow.mp hp).1
        (mem_primeWindow.mp hp).2.1 (mem_primeWindow.mp hq).2.1
    · simp only [hb, if_false]
      positivity
  rw [fourthRowTripleNoGate_switched_reorder] at hfinite
  have hclosed :
      (∑ c ∈ fourthRowTripleNoGateProfiles N δ W eleven, (convolutionCoeff W c.1 : ℝ) *
        (((omega3CofactorPrimeFibre N δ (5 / 2) c).filter
          (fun p => Sifted N (N - omega3CofactorValue c * p) Z)).card : ℝ)) ≤
      fourthRowTripleNoGateS N δ Z W eleven := by
    apply sum_le_sum
    rintro ⟨d, q, p, n⟩ hc
    obtain ⟨hd', hq, hp, _, hn, _, _⟩ := mem_omega3CofactorLabels.mp (mem_filter.mp hc).1
    have hepos : 0 < omega3CofactorValue ⟨d, q, p, n⟩ :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hd d hd') hn) (mem_primeWindow.mp hp).1.pos)
        (mem_primeWindow.mp hq).1.pos
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact_mod_cast card_le_card (filter_subset_filter _ (omega3_prime_fibre_subset_closed hepos))
  exact hfinite.trans (add_le_add (add_le_add hclosed le_rfl) le_rfl)

theorem fourthRowTripleNoGate_switching_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
        fourthRowMotherPrefixSum N δ (convolutionWuWindows N Δ V) (fourthRowTripleNoGateWord eleven) ≤
          fourthRowTripleNoGateS N δ (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
            (convolutionWuWindows N Δ V) eleven +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT1, hbad⟩ := omega3_badD_relative k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hexc⟩ := omega3_exceptional_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb eleven
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hf := fourthRowTripleNoGate_switching_finite (δ := δ) (convolutionWuWindows N Δ V) eleven
    (hT1.trans hN1) he (fun d hd =>
      (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1)
  have h1 := hbad N hN1 he i Δ V hb (5 / 2) (103 / 25) (by norm_num) (by norm_num) (by norm_num)
  have h2 := hexc N hN2 he i Δ V hb (5 / 2) (103 / 25) (by norm_num) (by norm_num) (by norm_num)
  linarith

end Wu2008DoubleSieve
