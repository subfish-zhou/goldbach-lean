import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateProfiles

/-! # Modulus-independent Fin2 layers of the actual filtered profiles -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem fourthRowTripleNoGate_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {c : Omega3CofactorIndex} {eleven : Bool}
    (hc : c ∈ fourthRowTripleNoGateProfiles N δ (convolutionWuWindows N Δ V) eleven) :
    0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3CofactorValue c ∧
      (omega3CofactorValue c : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
      2 ≤ c.2.1 ∧
      (c.2.1 : ℝ) ≤ min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 (5 / 2)) ∧
      (omega3CofactorValue c : ℝ) *
        min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 (5 / 2)) ≤ N := by
  have hc0 := (mem_filter.mp hc).1
  have hg := omega3_cofactor_actual_profile_geometry hN hδ hδhi hb
    (by norm_num : (2 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 103 / 25)
    (by norm_num : (103 / 25 : ℝ) ≤ 10) hc0
  obtain ⟨d, q, p, n⟩ := c
  obtain ⟨hd, hq, hp, _, hn, hsize, _⟩ := mem_omega3CofactorLabels.mp hc0
  have hd0 := (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  have he : 0 < omega3CofactorValue ⟨d, q, p, n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd0 hn) (mem_primeWindow.mp hp).1.pos)
      (mem_primeWindow.mp hq).1.pos
  have heN : omega3CofactorValue ⟨d, q, p, n⟩ ≤ N :=
    (Nat.le_mul_of_pos_right _ (mem_primeWindow.mp hq).1.pos).trans hsize
  exact ⟨he, heN, hg.1, hg.2.1, (mem_primeWindow.mp hq).1.two_le,
    hg.2.2.2.1, hg.2.2.2.2.2.2⟩

theorem fourthRowTripleNoGate_layers (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      let L := fourthRowTripleNoGateProfiles N δ W eleven
      (∀ e, (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤
        omega3LayerConstant k δ) ∧
      (∀ e, (omega3LayerFibre L e).card ≤ omega3LayerCount k δ) ∧
      (∀ j e, 0 ≤ omega3LayerCoefficient W L j e ∧
        omega3LayerCoefficient W L j e ≤ omega3LayerConstant k δ) := by
  obtain ⟨T, hT4, hf⟩ := omega3_cofactor_labels_fibre_uniform k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb eleven W L
  have hfull := hf N hN i Δ V hb (5 / 2) (103 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  have hw (e : ℕ) : (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤
      omega3LayerConstant k δ := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg
      (filter_subset_filter _ (fourthRowTripleNoGate_profiles_subset N δ W eleven))
      (fun _ _ _ => Nat.cast_nonneg _))
    exact hfull e
  refine ⟨hw, ?_, fun j e => ⟨omega3LayerCoefficient_nonneg W L j e,
    omega3LayerCoefficient_le W L j e (omega3LayerConstant_pos k δ).le (hw e)⟩⟩
  intro e
  have hh : ((omega3LayerFibre L e).card : ℝ) ≤
      ∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    apply sum_le_sum
    intro c hc
    exact_mod_cast omega3_cofactor_label_coefficient_pos
      (mem_filter.mp (mem_filter.mp hc).1).1
  exact_mod_cast hh.trans ((hw e).trans (Nat.le_ceil (omega3LayerConstant k δ)))

end Wu2008DoubleSieve
