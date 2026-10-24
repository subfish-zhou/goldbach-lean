import WR2GammaHighLowerTripleUnitPaid
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughMassScalar

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

noncomputable def finiteBuchstabMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ legalPrimeTriples N δ (Wu04RemainingCore.row j) k d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Literal nonunit scalar error; the separate unitMass is not multiplied by tau. -/
noncomputable def finiteErrorMass (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ legalPrimeTriples N δ (Wu04RemainingCore.row j) k d,
      ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Preserve the entire unit mass and restrict only the nonunit Buchstab main. -/
theorem rough_mass_finite_buchstab {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 6,
      (roughFamily j N δ k).mass ≤ unitMass j N δ k +
        finiteBuchstabMain j N δ k + τ * finiteErrorMass j N δ k := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨T,hT,hscalar⟩ := InclusiveRoughUniform.uniform_product_upper hη hτ
  refine ⟨T,hT,?_⟩
  intro N hN j k
  let W := windows j N
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) h
  have hterm : ∀ d ∈ boxConvolutionSupport W, ∀ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
      ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ) ≤
      (if tupleProduct d t ≤ N then 1 else 0) +
      (if tupleProduct d t * t.2.1 ≤ N then
        (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.2.1)+τ) *
          ((N : ℝ)/tupleProduct d t)/log t.2.1 else 0) := by
    intro d hd' t ht
    have hD := tupleProduct_pos (hd d hd') ht
    have hy := (window_lower j (by omega : 2 ≤ N) hδ hδhi hd'
      (mem_primeTriples.mp ht).2.1).2
    exact hscalar N hN _ _ hD hy
  rw [rough_mass_triple_dictionary]
  change (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
      ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
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

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.rough_mass_finite_buchstab
