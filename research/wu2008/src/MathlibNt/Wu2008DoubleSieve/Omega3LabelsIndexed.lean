import MathlibNt.Wu2008DoubleSieve.Omega3Switching

/-!
# Explicit finite indexed original and switched multisets

An index stores d,p3,p2,p1 and the final fibre coordinate. In the original
multiset the final coordinate is ell; in the switched multiset it is n.
The coefficient is attached once to the retained d coordinate.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

abbrev Omega3Index := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

noncomputable def omega3OriginalLabels {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3Index :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)).sigma fun p3 =>
      (primeWindow N (wuLocalCutoff N δ d t) (p3 : ℝ)).sigma fun p2 =>
        (primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ)).sigma fun p1 =>
          sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)

noncomputable def omega3SwitchedLabels {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3Index :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)).sigma fun p3 =>
      (primeWindow N (wuLocalCutoff N δ d t) (p3 : ℝ)).sigma fun p2 =>
        (primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ)).sigma fun p1 =>
          omega3SwitchedFibre N d p1 p2 p3

def omega3IndexCofactor (a : Omega3Index) : ℕ :=
  omega3Cofactor a.1 a.2.2.2.1 a.2.2.1 a.2.2.2.2

def omega3IndexOutput (N : ℕ) (a : Omega3Index) : ℕ :=
  N - omega3IndexCofactor a * a.2.1

theorem mem_omega3OriginalLabels {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {d p1 p2 p3 ell : ℕ} :
    (⟨d, p3, p2, p1, ell⟩ : Omega3Index) ∈ omega3OriginalLabels N δ s t W ↔
      d ∈ boxConvolutionSupport W ∧
      p3 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
      p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (p3 : ℝ) ∧
      p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ) ∧
      ell ∈ sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ) := by
  simp only [omega3OriginalLabels, mem_sigma]

theorem mem_omega3SwitchedLabels {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {d p1 p2 p3 n : ℕ} :
    (⟨d, p3, p2, p1, n⟩ : Omega3Index) ∈ omega3SwitchedLabels N δ s t W ↔
      d ∈ boxConvolutionSupport W ∧
      p3 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
      p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (p3 : ℝ) ∧
      p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ) ∧
      n ∈ omega3SwitchedFibre N d p1 p2 p3 := by
  simp only [omega3SwitchedLabels, mem_sigma]

theorem omega3_switched_label_size {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {d p1 p2 p3 n : ℕ}
    (ha : (⟨d, p3, p2, p1, n⟩ : Omega3Index) ∈ omega3SwitchedLabels N δ s t W) :
    0 < n ∧ omega3Cofactor d p1 p2 n * p3 ≤ N ∧
      omega3Cofactor d p1 p2 n * p2 ≤ N ∧
      (p3 : ℝ) < wuLocalCutoff N δ d s ∧
      Omega3Strengthened N d p1 p2 n := by
  obtain ⟨_, h3, h2, _, hn⟩ := mem_omega3SwitchedLabels.mp ha
  obtain ⟨_, hnpos, hsize, hgood⟩ := mem_filter.mp hn
  have h23 : p2 ≤ p3 := by exact_mod_cast (mem_primeWindow.mp h2).2.2.2.le
  exact ⟨hnpos, hsize, (Nat.mul_le_mul_left _ h23).trans hsize,
    (mem_primeWindow.mp h3).2.2.2, hgood⟩

theorem omega3_original_labels_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3OriginalLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      omega3LabelSum N δ s t W fun d p1 p2 p3 =>
        ∑ ell ∈ sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ),
          f ⟨d, p3, p2, p1, ell⟩ := by
  simp only [omega3OriginalLabels, omega3LabelSum, sum_sigma, mul_sum]

theorem omega3_switched_labels_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3SwitchedLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      omega3LabelSum N δ s t W fun d p1 p2 p3 =>
        ∑ n ∈ omega3SwitchedFibre N d p1 p2 p3, f ⟨d, p3, p2, p1, n⟩ := by
  simp only [omega3SwitchedLabels, omega3LabelSum, sum_sigma, mul_sum]

theorem wuOmega3Sum_eq_indexed_count {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) :
    wuOmega3Sum N δ s t W =
      ∑ a ∈ omega3OriginalLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) := by
  have h := omega3_original_labels_sum N δ s t W (fun _ => 1)
  simpa only [mul_one, sum_const, nsmul_eq_mul, mul_one,
    ← wuOmega3Sum_eq_original_label_count] using h.symm

theorem omega3_switched_sifted_eq_indexed_count {i : ℕ} (N : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) :
    omega3SwitchedSiftedCount N δ s t Z W =
      ∑ a ∈ (omega3SwitchedLabels N δ s t W).filter
        (fun a => Sifted N (omega3IndexOutput N a) Z), (convolutionCoeff W a.1 : ℝ) := by
  rw [sum_filter]
  have h := omega3_switched_labels_sum N δ s t W
    (fun a => if Sifted N (omega3IndexOutput N a) Z then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  simp only [omega3SwitchedSiftedCount, omega3SiftedSwitchedFibre,
    omega3IndexOutput, omega3IndexCofactor, card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rfl

theorem omega3_original_filtered_eq_indexed_count {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (P : ℕ → ℕ → Prop) :
    (omega3LabelSum N δ s t W fun d p1 p2 p3 =>
      ((sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
        (P d)).card) =
      ∑ a ∈ (omega3OriginalLabels N δ s t W).filter
        (fun a => P a.1 a.2.2.2.2), (convolutionCoeff W a.1 : ℝ) := by
  rw [sum_filter]
  have h := omega3_original_labels_sum N δ s t W
    (fun a => if P a.1 a.2.2.2.2 then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Grouping by e sums every original indexed contribution over its fibre.
The fibre still retains d,p1,p2,n,p3; no reconstruction or uniqueness is asserted. -/
theorem omega3_switched_cofactor_fibres {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3SwitchedLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      ∑ e ∈ (omega3SwitchedLabels N δ s t W).image omega3IndexCofactor,
        ∑ a ∈ (omega3SwitchedLabels N δ s t W).filter (fun a => omega3IndexCofactor a = e),
          (convolutionCoeff W a.1 : ℝ) * f a := by
  exact (sum_fiberwise_of_maps_to (fun _ ha => mem_image_of_mem _ ha) _).symm

/-- Regrouping original counts by prime output retains its full weighted
fibre, including all selected-prime triples and source coefficient labels. -/
theorem omega3_original_output_fibres {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3OriginalLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      ∑ ell ∈ (omega3OriginalLabels N δ s t W).image (fun a => a.2.2.2.2),
        ∑ a ∈ (omega3OriginalLabels N δ s t W).filter (fun a => a.2.2.2.2 = ell),
          (convolutionCoeff W a.1 : ℝ) * f a := by
  exact (sum_fiberwise_of_maps_to (fun _ ha => mem_image_of_mem _ ha) _).symm

end Wu2008DoubleSieve
