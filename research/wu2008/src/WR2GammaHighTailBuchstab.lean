import WR2GammaHighTailRoughMass
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassScalar

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

noncomputable def finiteBuchstabMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) k d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Literal scalar-error ledger, retaining all convolution multiplicities; not paid. -/
noncomputable def finiteErrorMass (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) k d,
      ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- The actual nonunit raw mass reaches its legal finite Buchstab main. -/
theorem rough_mass_finite_buchstab {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Bool,
      (roughFamily j N δ k).mass ≤ finiteBuchstabMain j N δ k + τ*finiteErrorMass j N δ k := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨T,hT,hscalar⟩ := NonunitRoughUniform.uniform_upper hη hτ
  refine ⟨T,hT,?_⟩
  intro N hN j k
  let W := windows j N
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) h
  have hterm : ∀ d ∈ boxConvolutionSupport W,
      ∀ t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) k d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ) ≤
      if tupleProduct d t * t.2.1 ≤ N then
        (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.2.1)+τ) *
          ((N : ℝ)/tupleProduct d t)/log t.2.1 else 0 := by
    intro d hd' t ht
    have hD := tupleProduct_pos (hd d hd') ht
    have hD1 : (1 : ℝ) ≤ tupleProduct d t := by exact_mod_cast hD
    have hx : (N : ℝ)/tupleProduct d t ≤ N :=
      div_le_self (Nat.cast_nonneg N) hD1
    have hy := (LowerTriple.window_lower j (by omega : 2 ≤ N) hδ hδhi hd'
      (mem_primeTuples.mp ht).2.1).2
    obtain ⟨hz,hu⟩ := hscalar N hN _ _ hx hy
    by_cases hg : tupleProduct d t * t.2.1 ≤ N
    · rw [if_pos hg]
      exact hu ((legal_gate_iff N d t hD).mp hg)
    · rw [if_neg hg, hz (lt_of_not_ge (fun h => hg ((legal_gate_iff N d t hD).mpr h)))]
      norm_num
  rw [rough_mass_tuple_dictionary]
  change (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) k d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) k d,
          if tupleProduct d t * t.2.1 ≤ N then
            (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.2.1)+τ) *
              ((N : ℝ)/tupleProduct d t)/log t.2.1 else 0 := by
      apply sum_le_sum
      intro d hd'
      exact mul_le_mul_of_nonneg_left (sum_le_sum (hterm d hd')) (Nat.cast_nonneg _)
    _ = _ := by
      unfold finiteBuchstabMain finiteErrorMass legalPrimeTuples
      simp only [sum_filter, mul_sum, Finset.mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro t _
      split_ifs <;> ring

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.rough_mass_finite_buchstab
