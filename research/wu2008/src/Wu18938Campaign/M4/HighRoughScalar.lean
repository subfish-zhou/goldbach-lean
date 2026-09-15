import Wu18938Campaign.M4.HighRoughDictionary
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassScalar

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real LiLiuPrereqBuchstab
open scoped Classical

def originalFiniteMain (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
      buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) *
        ((N : ℝ) / tupleProduct d t) / log t.2.1

def originalFiniteError (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
      ((N : ℝ) / tupleProduct d t) / log t.2.1

theorem original_rough_finite_buchstab {τ : ℝ} (htau : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ high : Bool,
      originalRoughMass j N δ high ≤
        originalFiniteMain j N δ high + τ * originalFiniteError j N δ high := by
  obtain ⟨T, hT, hscalar⟩ := NonunitRoughUniform.uniform_upper
    (show (0 : ℝ) < 1 / 40 by norm_num) htau
  refine ⟨T, hT, ?_⟩
  intro δ hd hh N hN j high
  have hterm (d : ℕ) (hdm : d ∈ boxConvolutionSupport (windows j N))
      (t : PrimeTuple) (ht : t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) high d) :
      (((roughNumbers ((N : ℝ) / tupleProduct d t) t.2.1).erase 1).card : ℝ) ≤
        if tupleProduct d t * t.2.1 ≤ N then
          (buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) + τ) *
            ((N : ℝ) / tupleProduct d t) / log t.2.1 else 0 := by
    have hdw : d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N := by
      simpa only [support_eq] using hdm
    have hD := tupleProduct_pos (mem_primeWindow.mp hdw).1.pos ht
    have hD1 : (1 : ℝ) ≤ tupleProduct d t := by exact_mod_cast hD
    have hx := div_le_self (Nat.cast_nonneg N) hD1
    have hy := (original_label_bounds j (by omega) hd hh hdw
      (mem_primeTuples.mp ht).2.1).2.1
    obtain ⟨hz, hu⟩ := hscalar N hN _ _ hx hy
    by_cases hg : tupleProduct d t * t.2.1 ≤ N
    · rw [if_pos hg]
      exact hu ((legal_gate_iff N d t hD).mp hg)
    · rw [if_neg hg, hz (lt_of_not_ge (fun h => hg ((legal_gate_iff N d t hD).mpr h)))]
      norm_num
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
        ∑ t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) high d,
          if tupleProduct d t * t.2.1 ≤ N then
            (buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) + τ) *
              ((N : ℝ) / tupleProduct d t) / log t.2.1 else 0 := by
      apply sum_le_sum
      intro d hdm
      exact mul_le_mul_of_nonneg_left (sum_le_sum (hterm d hdm)) (Nat.cast_nonneg _)
    _ = _ := by
      unfold originalFiniteMain originalFiniteError legalPrimeTuples
      simp only [sum_filter, mul_sum, Finset.mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro t _
      split_ifs <;> ring

end Wu18938Campaign.M4
