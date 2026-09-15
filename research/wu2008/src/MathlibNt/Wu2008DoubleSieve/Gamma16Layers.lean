import MathlibNt.Wu2008DoubleSieve.Gamma16SieveFamily

/-! # Fixed, modulus-independent layers for the actual encoded Gamma16 family -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem gamma16_encoded_fibre_sum {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) (e : ℕ) :
    (∑ c ∈ omega3LayerFibre (gamma16EncodedProfiles N δ W) e,
      (convolutionCoeff W c.1 : ℝ)) =
      ∑ c ∈ (gamma16Profiles N δ W).filter (fun c => gamma16Cofactor c = e),
        (convolutionCoeff W c.1 : ℝ) := by
  have h := gamma16_encoded_sum N δ W
    (fun c => if omega3CofactorValue c = e then (1 : ℝ) else 0)
  simpa only [omega3LayerFibre, sum_filter, mul_ite, mul_one, mul_zero,
    gamma16_encode_value] using h

theorem gamma16_encoded_coefficient_pos {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    {c : Omega3CofactorIndex} (hc : c ∈ gamma16EncodedProfiles N δ W) :
    0 < convolutionCoeff W c.1 := by
  obtain ⟨⟨d, p3, p2, p1, n⟩, hcp, rfl⟩ := mem_image.mp hc
  exact mem_boxConvolutionSupport.mp (mem_gamma16Profiles.mp hcp).1

theorem gamma16_encoded_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {c : Omega3CofactorIndex}
    (hc : c ∈ gamma16EncodedProfiles N δ (convolutionWuWindows N Δ V)) :
    0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
      (omega3CofactorValue c).Coprime N ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3CofactorValue c ∧
      (omega3CofactorValue c : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
      2 ≤ c.2.1 ∧
      (c.2.1 : ℝ) ≤ min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 (5 / 2)) ∧
      (omega3CofactorValue c : ℝ) *
        min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 (5 / 2)) ≤ N := by
  obtain ⟨c, hcp, rfl⟩ := mem_image.mp hc
  have hg := gamma16_profile_geometry hN hδ hδhi hb hcp
  simp only [gamma16_encode_value]
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
      hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.1⟩

theorem gamma16_source_layers (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      let L := gamma16EncodedProfiles N δ W
      (∀ e, (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤
        gamma16FibreConstant k δ) ∧
      (∀ e, (omega3LayerFibre L e).card ≤ gamma16LayerCount k δ) ∧
      (∀ j e, 0 ≤ omega3LayerCoefficient W L j e ∧
        omega3LayerCoefficient W L j e ≤ gamma16FibreConstant k δ) ∧
      (∀ c ∈ L, ∀ q, q.Prime → q ∣ omega3CofactorValue c →
        (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ)) := by
  obtain ⟨T, hT, hs⟩ := gamma16_source_fibres k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb W L
  obtain ⟨hweight, hrough⟩ := hs N hN i Δ V hb
  have hf (e : ℕ) :
      (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤ gamma16FibreConstant k δ := by
    rw [gamma16_encoded_fibre_sum]
    exact hweight e
  have hF : 0 ≤ gamma16FibreConstant k δ := by unfold gamma16FibreConstant; positivity
  refine ⟨hf, ?_, fun j e => ⟨omega3LayerCoefficient_nonneg W L j e,
    omega3LayerCoefficient_le W L j e hF (hf e)⟩, ?_⟩
  · intro e
    have hc : ((omega3LayerFibre L e).card : ℝ) ≤
        ∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ) := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      apply sum_le_sum
      intro c hc
      exact_mod_cast gamma16_encoded_coefficient_pos (mem_filter.mp hc).1
    exact_mod_cast hc.trans ((hf e).trans (Nat.le_ceil (gamma16FibreConstant k δ)))
  · intro c hc
    obtain ⟨c, hcp, rfl⟩ := mem_image.mp hc
    simpa only [gamma16_encode_value] using hrough c hcp

theorem gamma16_family_R1_le_layers {i N D B : ℕ} {δ Z : ℝ}
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B)
    (hpos : ∀ c ∈ L, 0 < omega3CofactorValue c) :
    gamma16FamilyR1 N D δ Z W L ≤
      ∑ j ∈ range B, ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          omega3LayerCoefficient W L j e *
            omega3ProfileError N q e (omega3LayerLower L j e)
              (omega3LayerUpper N δ (5 / 2) L j e)| := by
  have h := omega3Layer_modulus_sum_le W L B hB (omega3SieveModuli N D Z)
    (fun q => (3 : ℝ) ^ q.primeFactors.card) (fun _ _ => by positivity)
    (fun q c => (omega3SieveAPCount N δ (5 / 2) c q : ℝ) -
      (omega3CofactorPrimeFibreLE N δ (5 / 2) c).card / (Nat.totient q : ℝ))
  apply h.trans_eq
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro q _
  congr 2
  apply sum_congr rfl
  intro e he
  have hm := omega3LayerLabel_mem (mem_filter.mp he).1
  rw [omega3Layer_prime_error_eq_profile (mem_filter.mp he).1 (hm.2 ▸ hpos _ hm.1)]

end Wu2008DoubleSieve