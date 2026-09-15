import MathlibNt.Wu2008DoubleSieve.Omega3LabelsIndexed
import MathlibNt.Wu2008DoubleSieve.Omega3ErrorBudget

/-! # A single actual exceptional-output count for the switching bridge -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def omega3ExceptionalOutputFibre (N d p1 p2 p3 : ℕ) (δ : ℝ) : Finset ℕ :=
  (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
    fun ell => ell ∈ omega3ExceptionalOutputs N δ

noncomputable def omega3ExceptionalOutputCount {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  omega3LabelSum N δ s t W fun d p1 p2 p3 =>
    (omega3ExceptionalOutputFibre N d p1 p2 p3 δ).card

/-- Small prime outputs and outputs dividing N are counted in one union,
without a second copy of labels lying in their intersection. -/
theorem omega3_fibre_switching_exceptional_bound {N d p1 p2 p3 : ℕ} {δ : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d)
    (h1 : p1.Prime) (h1N : p1.Coprime N) (h2N : p2.Coprime N) :
    (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).card ≤
      (omega3SiftedSwitchedFibre N d p1 p2 p3 (sqrt ((N : ℝ) ^ (1 / 2 - δ)))).card +
      (omega3BadDFibre N d p1 p2 p3).card +
      (omega3ExceptionalOutputFibre N d p1 p2 p3 δ).card := by
  let Z := sqrt ((N : ℝ) ^ (1 / 2 - δ))
  have hcover :
      sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ) ⊆
        (omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3) ∪
          omega3ExceptionalOutputFibre N d p1 p2 p3 δ := by
    intro ell hell
    by_cases hd' : Omega3BadD N d ell
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hell, hd'⟩))
    by_cases he : ell ∈ omega3ExceptionalOutputs N δ
    · exact mem_union_right _ (mem_filter.mpr ⟨hell, he⟩)
    have hp := (mem_filter.mp hell).2.1
    have hdiv : ¬ell ∣ N := fun h =>
      he (mem_omega3ExceptionalOutputs (by omega) hp (Or.inr h))
    have hlarge : Z ≤ (ell : ℝ) := by
      by_contra hl
      exact he (mem_omega3ExceptionalOutputs (by omega) hp (Or.inl (lt_of_not_ge hl)))
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hell, hd', hdiv, hlarge⟩))
  have hc := card_le_card hcover
  have h01 := card_union_le (omega3GoodOriginalFibre N d p1 p2 p3 Z)
    (omega3BadDFibre N d p1 p2 p3)
  have h012 := card_union_le
    (omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3)
    (omega3ExceptionalOutputFibre N d p1 p2 p3 δ)
  have hg := omega3_good_original_injects (p3 := p3) (Z := Z) hN heven hd h1 h1N h2N
  dsimp only [Z] at hc h01 h012 hg
  omega

theorem wuOmega3Sum_le_switched_add_badD_add_exceptional {i N : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} (hN : 4 ≤ N) (heven : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    wuOmega3Sum N δ s t W ≤
      omega3SwitchedSiftedCount N δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ))) W +
      omega3BadDCount N δ s t W +
      omega3ExceptionalOutputCount N δ s t W := by
  rw [wuOmega3Sum_eq_original_label_count]
  unfold omega3SwitchedSiftedCount omega3BadDCount omega3ExceptionalOutputCount
  rw [← omega3LabelSum_add, ← omega3LabelSum_add]
  apply omega3LabelSum_mono
  intro d hd' p3 _ p2 h2 p1 h1
  have h := omega3_fibre_switching_exceptional_bound (p3 := p3) (δ := δ) hN heven (hd d hd')
    (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h1).2.1 (mem_primeWindow.mp h2).2.1
  exact_mod_cast h

theorem omega3_exceptional_eq_indexed_count {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) :
    omega3ExceptionalOutputCount N δ s t W =
      ∑ a ∈ (omega3OriginalLabels N δ s t W).filter
        (fun a => a.2.2.2.2 ∈ omega3ExceptionalOutputs N δ), (convolutionCoeff W a.1 : ℝ) := by
  unfold omega3ExceptionalOutputCount omega3ExceptionalOutputFibre
  rw [sum_filter]
  have h := omega3_original_labels_sum N δ s t W
    (fun a => if a.2.2.2.2 ∈ omega3ExceptionalOutputs N δ then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end Wu2008DoubleSieve
