import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassFinite

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real LiLiuPrereqBuchstab
open scoped Classical

noncomputable def actualPrimeTuples (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (high : Bool) (d : ℕ) : Finset PrimeTuple :=
  primeTuples N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa1)
    (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
    (wuLocalCutoff N δ d p.s) (word high)

/-- The gate is the exact legal scalar domain, not a convention for omega below one. -/
noncomputable def legalPrimeTuples (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (high : Bool) (d : ℕ) : Finset PrimeTuple :=
  (actualPrimeTuples N δ p high d).filter fun t => tupleProduct d t * t.2.1 ≤ N

noncomputable def finiteBuchstabMain {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ legalPrimeTuples N δ p high d,
      buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
        ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Literal scalar-error ledger, with unchanged convolution multiplicities. -/
noncomputable def finiteErrorMass {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ legalPrimeTuples N δ p high d,
      ((N : ℝ)/tupleProduct d t) / log t.2.1

theorem legal_gate_iff (N d : ℕ) (t : PrimeTuple) (hD : 0 < tupleProduct d t) :
    tupleProduct d t * t.2.1 ≤ N ↔ (t.2.1 : ℝ) ≤ (N : ℝ)/tupleProduct d t := by
  rw [le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < tupleProduct d t)]
  simpa only [mul_comm] using
    (show tupleProduct d t * t.2.1 ≤ N ↔ (tupleProduct d t : ℝ) * t.2.1 ≤ N by
      exact_mod_cast Iff.rfl)

theorem legal_log_ratio {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    {high : Bool} {t : PrimeTuple} (hd : 0 < d)
    (ht : t ∈ legalPrimeTuples N δ p high d) :
    1 ≤ log ((N : ℝ)/tupleProduct d t) / log t.2.1 := by
  obtain ⟨ht,hcap⟩ := mem_filter.mp ht
  have hp := (mem_primeWindow.mp (mem_primeTuples.mp ht).2.1).1
  exact NonunitRoughUniform.log_ratio_ge_one
    (by exact_mod_cast hp.one_lt) ((legal_gate_iff N d t (tupleProduct_pos hd ht)).mp hcap)

/-- One scalar threshold, before every original box and both full words.
The finite reciprocal error is retained, not claimed paid. -/
theorem rough_mass_finite_buchstab (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
        (roughFamily N δ Δ V p high).mass ≤
          finiteBuchstabMain N δ Δ V p high + τ * finiteErrorMass N δ Δ V p high := by
  have hη : 0 < wuLocalExponent k δ / 10 := by
    exact div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T,hT,hscalar⟩ := NonunitRoughUniform.uniform_upper hη hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp high
  let W := convolutionWuWindows N Δ V
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) h
  have hterm : ∀ d ∈ boxConvolutionSupport W,
      ∀ t ∈ actualPrimeTuples N δ p high d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ) ≤
      if tupleProduct d t * t.2.1 ≤ N then
        (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.2.1)+τ) *
          ((N : ℝ)/tupleProduct d t)/log t.2.1 else 0 := by
    intro d hd' t ht
    have hD := tupleProduct_pos (hd d hd') ht
    have hD1 : (1 : ℝ) ≤ tupleProduct d t := by exact_mod_cast hD
    have hx : (N : ℝ)/tupleProduct d t ≤ N :=
      div_le_self (Nat.cast_nonneg N) hD1
    have hy := (mother_window_lower (by omega : 2 ≤ N) hδ hδhi hb p hp hd'
      (mem_primeTuples.mp ht).2.1).2
    obtain ⟨hz,hu⟩ := hscalar N hN _ _ hx hy
    by_cases hg : tupleProduct d t * t.2.1 ≤ N
    · rw [if_pos hg]
      exact hu ((legal_gate_iff N d t hD).mp hg)
    · rw [if_neg hg, hz (lt_of_not_ge (fun h => hg ((legal_gate_iff N d t hD).mpr h)))]
      norm_num
  rw [roughFamily_mass_dictionary]
  change (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ actualPrimeTuples N δ p high d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ t ∈ actualPrimeTuples N δ p high d,
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

theorem rough_mass_pair_finite_buchstab (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        (roughFamily N δ Δ V p false).mass + (roughFamily N δ Δ V p true).mass ≤
          finiteBuchstabMain N δ Δ V p false + finiteBuchstabMain N δ Δ V p true +
            τ * (finiteErrorMass N δ Δ V p false + finiteErrorMass N δ Δ V p true) := by
  obtain ⟨T,hT,h⟩ := rough_mass_finite_buchstab k hδ hδhi hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  have hpair := add_le_add (h N hN i Δ V hb p hp false) (h N hN i Δ V hb p hp true)
  simpa only [mul_add, add_assoc, add_left_comm, add_comm] using hpair

end Wu2008DoubleSieve.HighNonunit
