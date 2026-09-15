import MathlibNt.Wu2008DoubleSieve.Omega3MultiplicityCofactor
import MathlibNt.Wu2008DoubleSieve.Omega3LabelsIndexed

/-!
# The actual switched cofactor coefficient, with p3 kept separate

Projecting the switched index forgets only the separately ranged p3.
The exact test-function identity keeps every p3 in an inner fibre. The
bounded outer cofactor coefficient counts d,p2,p1,n, not varying p3.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def omega3ProjectCofactor (a : Omega3Index) : Omega3CofactorMultiplicityLabel :=
  ⟨a.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩

noncomputable def omega3ProjectedCofactorLabels {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3CofactorMultiplicityLabel :=
  (omega3SwitchedLabels N δ s t W).image omega3ProjectCofactor

noncomputable def omega3ActualCofactorFibre {i : ℕ} (N e : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3CofactorMultiplicityLabel :=
  (omega3ProjectedCofactorLabels N δ s t W).filter
    (fun a => omega3Cofactor a.1 a.2.2.1 a.2.1 a.2.2.2 = e)

/-- Exact grouping by the retained cofactor label. Every p3 and every
test-function value remains in the inner sum; its coefficient occurs once. -/
theorem omega3_projected_cofactor_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3SwitchedLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      ∑ b ∈ omega3ProjectedCofactorLabels N δ s t W, (convolutionCoeff W b.1 : ℝ) *
        ∑ a ∈ (omega3SwitchedLabels N δ s t W).filter
          (fun a => omega3ProjectCofactor a = b), f a := by
  have h := sum_fiberwise_of_maps_to
    (s := omega3SwitchedLabels N δ s t W)
    (t := omega3ProjectedCofactorLabels N δ s t W)
    (g := omega3ProjectCofactor)
    (fun _ ha => mem_image_of_mem _ ha)
    (fun a => (convolutionCoeff W a.1 : ℝ) * f a)
  rw [← h]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  have heq := congr_arg Sigma.fst (mem_filter.mp ha).2
  change a.1 = b.1 at heq
  rw [heq]

theorem omega3_actual_cofactor_fibre_subset {i N e : ℕ} {δ s t : ℝ}
    (W : Fin i → Finset ℕ) :
    omega3ActualCofactorFibre N e δ s t W ⊆
      omega3CofactorMultiplicityCarrier N e W
        (fun d => wuLocalCutoff N δ d t) (fun d => wuLocalCutoff N δ d s) := by
  intro b hb
  obtain ⟨hb, hprod⟩ := mem_filter.mp hb
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  rcases a with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hd, h3, h2, h1, hn⟩ := mem_omega3SwitchedLabels.mp ha
  have h := omega3_switched_mem_cofactor_carrier W
    (fun d => wuLocalCutoff N δ d t) (fun d => wuLocalCutoff N δ d s)
    hd h3 h2 h1 hn
  change omega3Cofactor d p1 p2 n = e at hprod
  simpa only [hprod, omega3ProjectCofactor] using h

theorem omega3_actual_cofactor_fibre_strengthened {i N e : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} {b : Omega3CofactorMultiplicityLabel}
    (hb : b ∈ omega3ActualCofactorFibre N e δ s t W) :
    Omega3Strengthened N b.1 b.2.2.1 b.2.1 b.2.2.2 := by
  obtain ⟨hb, _⟩ := mem_filter.mp hb
  obtain ⟨⟨d, p3, p2, p1, n⟩, ha, rfl⟩ := mem_image.mp hb
  have hn := (mem_omega3SwitchedLabels.mp ha).2.2.2.2
  exact (mem_filter.mp hn).2.2.2

/-- The actual projected cofactor coefficient is uniformly bounded.
The fibre contains no p3 coordinate, and retains all convolution weights. -/
theorem omega3_actual_cofactor_weight_le {i k N e : ℕ} {δ s t η : ℝ}
    (W : Fin i → Finset ℕ)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hlow : ∀ d ∈ boxConvolutionSupport W,
      (N : ℝ) ^ η ≤ wuLocalCutoff N δ d t) :
    (∑ a ∈ omega3ActualCofactorFibre N e δ s t W, (convolutionCoeff W a.1 : ℝ)) ≤
      (max 1 (1 / η)) ^ (k + 2) :=
  omega3_cofactor_subcarrier_weight_le W _ _ _
    (omega3_actual_cofactor_fibre_subset W) hik hN he heN hη hW hlow

end Wu2008DoubleSieve
