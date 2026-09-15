import StaircaseActualKernel

open Set MeasureTheory QuarterTrim Wu2008DoubleSieve
open scoped Classical

namespace StaircaseActual
noncomputable section

/-- Fubini on the literal mask; no integrability hypothesis is supplied. -/
theorem gamma_eq_uniform {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    StaircaseShrink.gamma t = 4 * ∫ v : ℝ × ℝ, uniformKernel t v := by
  rw [show (∫ v : ℝ × ℝ, uniformKernel t v) =
    ∫ x, ∫ y, uniformKernel t (x,y) from integral_prod _ (uniform_integrable ht)]
  have hs : Function.support (fun x => ∫ y, uniformKernel t (x,y)) ⊆ Icc alpha beta := by
    intro x hx
    by_contra h
    apply hx
    have he : (fun y => uniformKernel t (x,y)) = 0 := by
      funext y
      have hn : (x,y) ∉ StaircaseShrink.domain t := fun hv => h hv.1
      simp [uniformKernel,hn]
    change (∫ y, uniformKernel t (x,y)) = 0
    rw [he]
    simp
  rw [truncatedSixthMass_integral_eq_interval StaircaseShrink.fixed_bounds.2.1.le hs]
  unfold StaircaseShrink.gamma
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le StaircaseShrink.fixed_bounds.2.1.le] at hx
  have he : (fun y => uniformKernel t (x,y)) =
      (Icc beta (StaircaseShrink.upper t x)).indicator (kernel Wu08Staircase.profile x) := by
    funext y
    simp only [uniformKernel,StaircaseShrink.domain,mem_ofPred_eq,hx,true_and,indicator]
    split_ifs <;> rfl
  change (∫ y in beta..StaircaseShrink.upper t x, kernel Wu08Staircase.profile x y) =
    ∫ y, uniformKernel t (x,y)
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.integral_of_le (StaircaseShrink.upper_ge ht' hx.2)

/-- The same literal shrunken 21-step integral enters the existing h coefficient. -/
theorem gamma_payment {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2) (hn : NodeCertificate δ) :
    StaircaseShrink.gamma t ≤ truncatedSixthLowerHadmdelta δ := by
  rw [gamma_eq_uniform ht.le ht', (truncatedSixthMass_literal_integrals hδ (by linarith)).2]
  exact mul_le_mul_of_nonneg_left
    (integral_mono (uniform_integrable ht.le)
      (truncatedSixthMass_kernels_integrable hδ (by linarith)).2
      (uniform_le_actual ht ht' hδ hδt hn)) (by norm_num)

/-- The node certificate is an explicitly unsupplied finite input for each delta.
The original producer supplies the common threshold and every actual moving prime window. -/
theorem actual_lower {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (ht' : t ≤ 1/1000) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ t/2 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 → NodeCertificate δ →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin + StaircaseShrink.gamma t - ε)*
            wuSingularSeries N*N/Real.log N^(2 : ℕ) ≤
          (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
            ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
            ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨a,ha,_,hc⟩ := truncatedSixthZeroDelta_actual_lower hε
  refine ⟨min a (t/2),lt_min ha (half_pos ht),min_le_right _ _,?_⟩
  intro δ hδ hδsmall hn
  obtain ⟨T,hT,htN⟩ := hc δ hδ (hδsmall.trans_le (min_le_left _ _))
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hg := gamma_payment ht ht' hδ (hδsmall.le.trans (min_le_right _ _)) hn
  have hm := mul_le_mul_of_nonneg_right
    (show truncatedSixthLowerF6lin+StaircaseShrink.gamma t-ε ≤
      truncatedSixthLowerF6lin+truncatedSixthLowerHadmdelta δ-ε by linarith)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hm' : (truncatedSixthLowerF6lin+StaircaseShrink.gamma t-ε)*
      wuSingularSeries N*N/Real.log N^(2 : ℕ) ≤
      (truncatedSixthLowerF6lin+truncatedSixthLowerHadmdelta δ-ε)*
      wuSingularSeries N*N/Real.log N^(2 : ℕ) := by
    simpa only [truncatedSixthMassScale,mul_div_assoc,mul_assoc] using hm
  exact hm'.trans (htN N hN he)

end
end StaircaseActual
