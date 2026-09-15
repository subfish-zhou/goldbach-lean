import MathlibNt.Wu2008DoubleSieve.Omega3LayerResidual

/-!
# Actual common-profile interface and explicit coefficient normalization

The unsplit coefficient is bounded by C, not by 1. If a later distribution
theorem requires a coefficient in [0,1], divide by C and retain exactly one
factor C outside the entire layer sum. No distribution theorem is assumed.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem omega3LayerConstant_pos (k : ℕ) (δ : ℝ) :
    0 < omega3LayerConstant k δ := by
  unfold omega3LayerConstant
  positivity

noncomputable def omega3LayerNormalizedCoefficient {i : ℕ} (k : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) (j e : ℕ) : ℝ :=
  omega3LayerCoefficient W L j e / omega3LayerConstant k δ

theorem omega3LayerNormalizedCoefficient_bounds {i : ℕ} (k : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) (j e : ℕ)
    (hbound : omega3LayerCoefficient W L j e ≤ omega3LayerConstant k δ) :
    0 ≤ omega3LayerNormalizedCoefficient k δ W L j e ∧
      omega3LayerNormalizedCoefficient k δ W L j e ≤ 1 := by
  exact ⟨div_nonneg (omega3LayerCoefficient_nonneg W L j e)
    (omega3LayerConstant_pos k δ).le,
    (div_le_one (omega3LayerConstant_pos k δ)).mpr hbound⟩

theorem omega3Layer_cofactor_test_sum {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B)
    (F : ℕ → Omega3CofactorIndex → ℝ) :
    (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * F (omega3CofactorValue c) c) =
      ∑ j ∈ range B, ∑ e ∈ omega3LayerSupport L j,
        omega3LayerCoefficient W L j e * F e (omega3LayerLabel L j e) := by
  rw [omega3Layer_weighted_sum W L B hB]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro e he
  rw [(omega3LayerLabel_mem he).2]

theorem omega3Layer_normalized_test_sum {i : ℕ} (k : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B)
    (F : ℕ → Omega3CofactorIndex → ℝ) :
    (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * F (omega3CofactorValue c) c) =
      omega3LayerConstant k δ *
        ∑ j ∈ range B, ∑ e ∈ omega3LayerSupport L j,
          omega3LayerNormalizedCoefficient k δ W L j e *
            F e (omega3LayerLabel L j e) := by
  rw [omega3Layer_cofactor_test_sum W L B hB F, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]
  apply sum_congr rfl
  intro e _
  unfold omega3LayerNormalizedCoefficient
  field_simp [ne_of_gt (omega3LayerConstant_pos k δ)]

/-- A single actual-source theorem supplies the bounded number of common
layers, both coefficient conventions, all endpoint geometry and an exact
identity for arbitrary tests retaining both the cofactor and the full label.
The two endpoints may coincide. -/
theorem omega3_cofactor_common_profile_layers (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let W := convolutionWuWindows N Δ V
      let L := omega3CofactorLabels N δ s t W
      (∀ e, (omega3LayerFibre L e).card ≤ omega3LayerCount k δ) ∧
      (∀ j e,
        0 ≤ omega3LayerCoefficient W L j e ∧
        omega3LayerCoefficient W L j e ≤ omega3LayerConstant k δ ∧
        0 ≤ omega3LayerNormalizedCoefficient k δ W L j e ∧
        omega3LayerNormalizedCoefficient k δ W L j e ≤ 1) ∧
      (∀ j e, e ∈ omega3LayerSupport L j →
        omega3LayerLabel L j e ∈ L ∧
        omega3CofactorValue (omega3LayerLabel L j e) = e ∧
        0 < omega3LayerCoefficient W L j e ∧
        (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ e ∧
        (e : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
        (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3LayerLower L j e ∧
        omega3LayerLower L j e ≤ omega3LayerUpper N δ s L j e ∧
        (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3LayerUpper N δ s L j e ∧
        (e : ℝ) * omega3LayerLower L j e ≤ N ∧
        (e : ℝ) * omega3LayerUpper N δ s L j e ≤ N) ∧
      (∀ F : ℕ → Omega3CofactorIndex → ℝ,
        (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * F (omega3CofactorValue c) c) =
          ∑ j ∈ range (omega3LayerCount k δ), ∑ e ∈ omega3LayerSupport L j,
            omega3LayerCoefficient W L j e * F e (omega3LayerLabel L j e)) ∧
      (∀ F : ℕ → Omega3CofactorIndex → ℝ,
        (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * F (omega3CofactorValue c) c) =
          omega3LayerConstant k δ *
            ∑ j ∈ range (omega3LayerCount k δ), ∑ e ∈ omega3LayerSupport L j,
              omega3LayerNormalizedCoefficient k δ W L j e *
                F e (omega3LayerLabel L j e)) := by
  obtain ⟨T, hT4, hT⟩ := omega3_cofactor_layers_bounded k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht W L
  obtain ⟨hcard, hcoeff, _⟩ := hT N hN i Δ V hb s t hs hst ht
  refine ⟨hcard, ?_, ?_, omega3Layer_cofactor_test_sum W L _ hcard,
    omega3Layer_normalized_test_sum k δ W L _ hcard⟩
  · intro j e
    exact ⟨(hcoeff j e).1, (hcoeff j e).2,
      omega3LayerNormalizedCoefficient_bounds k δ W L j e (hcoeff j e).2⟩
  · intro j e he
    have hlabel := omega3LayerLabel_mem he
    refine ⟨hlabel.1, hlabel.2, ?_, ?_⟩
    · rw [omega3LayerCoefficient_eq W he]
      exact_mod_cast omega3_cofactor_label_coefficient_pos hlabel.1
    · exact omega3Layer_actual_geometry (hT4.trans hN |>.trans' (by norm_num))
        hδ hδhi hb hs hst ht he

end Wu2008DoubleSieve
