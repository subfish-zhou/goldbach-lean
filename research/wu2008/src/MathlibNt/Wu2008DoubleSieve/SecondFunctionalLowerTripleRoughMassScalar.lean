import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughMassFinite
import MathlibNt.Wu2008DoubleSieve.InclusiveRoughProduct

namespace Wu2008DoubleSieve.LowerTripleGroupedFinite
open Finset Real LiLiuPrereqBuchstab
open scoped Classical

/-- Only the nonunit main term is restricted by this legal gate. -/
noncomputable def legalPrimeTriples (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) : Finset PrimeTriple :=
  (actualPrimeTriples N δ p j d).filter fun t => tupleProduct d t * t.2.1 ≤ N

noncomputable def finiteBuchstabMain {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ legalPrimeTriples N δ p j d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Literal nonunit scalar error; the separate unitMass is not multiplied by tau. -/
noncomputable def finiteErrorMass {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ legalPrimeTriples N δ p j d,
      ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Actual rough raw mass, with its full unit term and an unpaid nonunit scalar error. -/
theorem rough_mass_finite_buchstab (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
        (LowerTripleGrouped.roughFamily N δ Δ V p j).mass ≤
          unitMass N δ Δ V p j + finiteBuchstabMain N δ Δ V p j +
            τ * finiteErrorMass N δ Δ V p j := by
  have hη : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T,hT,hscalar⟩ := InclusiveRoughUniform.uniform_product_upper hη hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  let W := convolutionWuWindows N Δ V
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) h
  have hterm : ∀ d ∈ boxConvolutionSupport W, ∀ t ∈ actualPrimeTriples N δ p j d,
      ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ) ≤
      (if tupleProduct d t ≤ N then 1 else 0) +
      (if tupleProduct d t * t.2.1 ≤ N then
        (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.2.1)+τ) *
          ((N : ℝ)/tupleProduct d t)/log t.2.1 else 0) := by
    intro d hd' t ht
    have hD := tupleProduct_pos (hd d hd') ht
    have hy := (HighNonunit.mother_window_lower (by omega : 2 ≤ N) hδ hδhi hb p hp hd'
      (mem_primeTriples.mp ht).2.1).2
    exact hscalar N hN _ _ hD hy
  rw [rough_mass_triple_dictionary]
  change (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ actualPrimeTriples N δ p j d,
      ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ t ∈ actualPrimeTriples N δ p j d,
          ((if tupleProduct d t ≤ N then 1 else 0) +
           (if tupleProduct d t * t.2.1 ≤ N then
             (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.2.1)+τ) *
               ((N : ℝ)/tupleProduct d t)/log t.2.1 else 0)) := by
      apply sum_le_sum
      intro d hd'
      exact mul_le_mul_of_nonneg_left (sum_le_sum (hterm d hd')) (Nat.cast_nonneg _)
    _ = _ := by
      unfold unitMass finiteBuchstabMain finiteErrorMass legalPrimeTriples
      simp only [sum_filter, mul_sum, Finset.mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro t _
      split_ifs <;> ring

/-- One tau multiplies the complete six-band nonunit error, not the unit contribution. -/
theorem rough_mass_six_finite_buchstab (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        (∑ j : Fin 6, (LowerTripleGrouped.roughFamily N δ Δ V p j).mass) ≤
          (∑ j : Fin 6, unitMass N δ Δ V p j) +
          (∑ j : Fin 6, finiteBuchstabMain N δ Δ V p j) +
          τ * ∑ j : Fin 6, finiteErrorMass N δ Δ V p j := by
  obtain ⟨T,hT,h⟩ := rough_mass_finite_buchstab k hδ hδhi hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  simpa only [sum_add_distrib, ← mul_sum] using
    sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => h N hN i Δ V hb p hp j)

end Wu2008DoubleSieve.LowerTripleGroupedFinite
