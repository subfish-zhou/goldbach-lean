import MathlibNt.Wu2008DoubleSieve.Omega3LayerFinite

/-!
# Uniformly bounded actual weighted layers

Convolution multiplicities are positive integers on every actual label,
including labels with empty prime fibres. This justifies bounding the number
of labels by the proved weighted fibre mass; no uniqueness claim is used.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3LayerConstant (k : ℕ) (δ : ℝ) : ℝ :=
  (max 1 (1 / (wuLocalExponent k δ / 10))) ^ (k + 2)

noncomputable def omega3LayerCount (k : ℕ) (δ : ℝ) : ℕ :=
  ⌈omega3LayerConstant k δ⌉₊

theorem omega3LayerConstant_nonneg (k : ℕ) (δ : ℝ) :
    0 ≤ omega3LayerConstant k δ := by
  unfold omega3LayerConstant
  positivity

theorem omega3_cofactor_label_coefficient_pos {i N : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s t W) :
    0 < convolutionCoeff W c.1 := by
  rcases c with ⟨d, p2, p1, n⟩
  exact mem_boxConvolutionSupport.mp (mem_omega3CofactorLabels.mp hc).1

/-- The coefficient really is a positive integer, before any cardinality
comparison is made. It is not the cardinality of the varying-prime fibre. -/
theorem omega3_cofactor_label_coefficient_integer {i N : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s t W) :
    ∃ m : ℕ, 0 < m ∧ (convolutionCoeff W c.1 : ℝ) = m :=
  ⟨convolutionCoeff W c.1, omega3_cofactor_label_coefficient_pos hc, rfl⟩

theorem omega3_cofactor_fibre_card_le_weight {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (e : ℕ) :
    ((omega3LayerFibre (omega3CofactorLabels N δ s t W) e).card : ℝ) ≤
      ∑ c ∈ omega3LayerFibre (omega3CofactorLabels N δ s t W) e,
        (convolutionCoeff W c.1 : ℝ) := by
  calc
    _ = ∑ _c ∈ omega3LayerFibre (omega3CofactorLabels N δ s t W) e, (1 : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
      apply sum_le_sum
      intro c hc
      exact_mod_cast omega3_cofactor_label_coefficient_pos (mem_filter.mp hc).1

noncomputable def omega3LayerCoefficient {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (j e : ℕ) : ℝ :=
  if e ∈ omega3LayerSupport L j then (convolutionCoeff W (omega3LayerLabel L j e).1 : ℝ)
  else 0

theorem omega3LayerCoefficient_eq {i : ℕ} (W : Fin i → Finset ℕ)
    {L : Finset Omega3CofactorIndex} {j e : ℕ} (he : e ∈ omega3LayerSupport L j) :
    omega3LayerCoefficient W L j e = convolutionCoeff W (omega3LayerLabel L j e).1 := by
  exact if_pos he

theorem omega3LayerCoefficient_integer {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (j e : ℕ) :
    ∃ m : ℕ, omega3LayerCoefficient W L j e = m := by
  by_cases he : e ∈ omega3LayerSupport L j
  · exact ⟨_, omega3LayerCoefficient_eq W he⟩
  · exact ⟨0, by simp only [omega3LayerCoefficient, if_neg he, Nat.cast_zero]⟩

theorem omega3LayerCoefficient_nonneg {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (j e : ℕ) :
    0 ≤ omega3LayerCoefficient W L j e := by
  obtain ⟨m, hm⟩ := omega3LayerCoefficient_integer W L j e
  rw [hm]
  exact Nat.cast_nonneg m

theorem omega3LayerCoefficient_le {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (j e : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hweight : (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤ C) :
    omega3LayerCoefficient W L j e ≤ C := by
  by_cases he : e ∈ omega3LayerSupport L j
  · rw [omega3LayerCoefficient_eq W he]
    exact (single_le_sum (f := fun c : Omega3CofactorIndex => (convolutionCoeff W c.1 : ℝ))
      (fun _ _ => Nat.cast_nonneg _)
      (omega3LayerLabel_mem_fibre (mem_filter.mp he).2)).trans hweight
  · simpa only [omega3LayerCoefficient, if_neg he] using hC

theorem omega3Layer_weighted_sum {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B) (F : Omega3CofactorIndex → ℝ) :
    (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * F c) =
      ∑ j ∈ range B, ∑ e ∈ omega3LayerSupport L j,
        omega3LayerCoefficient W L j e * F (omega3LayerLabel L j e) := by
  rw [omega3Layer_sum L B hB]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro e he
  rw [omega3LayerCoefficient_eq W he]

/-- Fixed k,delta determine the number of layers before N or any source box
is chosen. The hypotheses are exactly those of the accepted fibre producer. -/
theorem omega3_cofactor_layers_bounded (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let W := convolutionWuWindows N Δ V
      let L := omega3CofactorLabels N δ s t W
      (∀ e, (omega3LayerFibre L e).card ≤ omega3LayerCount k δ) ∧
      (∀ j e, 0 ≤ omega3LayerCoefficient W L j e ∧
        omega3LayerCoefficient W L j e ≤ omega3LayerConstant k δ) ∧
      (∀ F : Omega3CofactorIndex → ℝ,
        (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * F c) =
          ∑ j ∈ range (omega3LayerCount k δ), ∑ e ∈ omega3LayerSupport L j,
            omega3LayerCoefficient W L j e * F (omega3LayerLabel L j e)) := by
  obtain ⟨T, hT4, hT⟩ := omega3_cofactor_labels_fibre_uniform k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht W L
  have hweight : ∀ e, (∑ c ∈ omega3LayerFibre L e,
      (convolutionCoeff W c.1 : ℝ)) ≤ omega3LayerConstant k δ :=
    hT N hN i Δ V hb s t hs hst ht
  have hcard : ∀ e, (omega3LayerFibre L e).card ≤ omega3LayerCount k δ := by
    intro e
    exact_mod_cast (omega3_cofactor_fibre_card_le_weight N δ s t W e).trans
      ((hweight e).trans (Nat.le_ceil (omega3LayerConstant k δ)))
  refine ⟨hcard, ?_, fun F => omega3Layer_weighted_sum W L _ hcard F⟩
  intro j e
  exact ⟨omega3LayerCoefficient_nonneg W L j e,
    omega3LayerCoefficient_le W L j e (omega3LayerConstant_nonneg k δ) (hweight e)⟩

end Wu2008DoubleSieve
