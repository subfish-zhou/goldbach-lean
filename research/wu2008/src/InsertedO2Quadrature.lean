import InsertedO2Geometry

namespace InsertedO2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2 HighO2Terminal
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- Consume the frozen selected-fibre quadrature on any genuinely admitted
box. All labelled convolution coefficients, true-li and d*N remain literal. -/
theorem selected_integral {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ,
      ∀ W : Fin i → Finset ℕ, (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |reboxingPrimeSum true N δ s t W (fun d p => f (ratio N d p δ t)) -
        (∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))) *
          boxTheta N ((N : ℝ)^(1/2-δ)) W| ≤
      ε * boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  obtain ⟨T,hT4,hfibre⟩ := selected_fibre_integral hε
  refine ⟨T,hT4,?_⟩
  intro N hN i W hW hsize f hf hfb s t hs hst ht ht5
  have hN4 := hT4.trans hN
  let Q := (N : ℝ)^(1/2-δ)
  let I := ∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ)*wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d))
  have hpos : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun d hd => boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
  have hg := fun d hd => residual_level (show 2 ≤ N by omega) hδ (hpos d hd) (hsize d hd)
  have hpoint : ∀ d ∈ boxConvolutionSupport W,
      |(∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d)))) - I| ≤ ε := by
    intro d hd
    exact hfibre N hN d (hpos d hd) (hg d hd).1 (Q/d) (hg d hd).2.1 f hf hfb s t hs hst ht ht5
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hd
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos (hpos d hd) (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hg d hd).2.2).le)
  have hli : 0 ≤ 4*logarithmicIntegral N := mul_nonneg (by norm_num)
    ((by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN4))
  change |4*logarithmicIntegral N*(∑ d ∈ boxConvolutionSupport W, w d *
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d)))) -
      I*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)
  rw [mul_left_comm I,← mul_sub,abs_mul,abs_of_nonneg hli,mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  rw [mul_comm I,sum_mul,← sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d*((∑ p ∈ primeWindow (d*N)
        (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d))))-I)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d*ε := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul,abs_of_nonneg (hw d hd)]
      exact mul_le_mul_of_nonneg_left (hpoint d hd) (hw d hd)
    _ = _ := by rw [← sum_mul,mul_comm]

end
end InsertedO2
