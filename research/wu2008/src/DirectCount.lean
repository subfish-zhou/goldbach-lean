import DirectLoss

open Set MeasureTheory QuarterTrim Wu2008DoubleSieve ActualNineFeedback
open scoped Classical

namespace DirectFiniteF6
noncomputable section

/-- A concrete coefficient on the original domain, with no actual h values in its definition. -/
def C (n : ℕ) : ℝ := Gamma (transferredLower n) 0

def E (n : ℕ) : ℝ := Gamma (transferredDebit n) 0

theorem transferredLower_nonneg (n : ℕ) (j : Fin 21) : 0 ≤ transferredLower n j :=
  matrixApply_nonneg NodeExtension.transferMatrix_nonneg (lowerIterate_nonneg n) j

theorem C_nonneg (n : ℕ) : 0 ≤ C n := Gamma_nonneg (transferredLower_nonneg n) le_rfl

theorem E_nonneg (n : ℕ) : 0 ≤ E n := Gamma_nonneg (transferredDebit_nonneg n) le_rfl

theorem C_monotone : Monotone C := by
  intro n m hnm
  apply Gamma_mono _ le_rfl
  intro j
  exact matrixApply_mono NodeExtension.transferMatrix_nonneg
    (fun k => lowerIterate_monotone k hnm) j

/-- Positive truncation keeps the denominator comparison in its legitimate direction. -/
theorem clipped_uniform_le_actual {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2) (n : ℕ) (v : ℝ × ℝ) :
    uniform (clipped n δ) t v ≤ truncatedSixthMassHKernel δ v := by
  by_cases hv : v ∈ StaircaseShrink.domain t
  · have hvt : truncatedSixthLowerAdmissibleRegion t v.1 v.2 := by
      have he := congrArg (fun S : Set (ℝ × ℝ) => v ∈ S) (StaircaseActual.domain_eq ht.le)
      exact he.mp hv
    have hvd := StaircaseActual.region_mono (show δ ≤ t by linarith) hvt
    rw [uniform, if_pos hv, truncatedSixthMassHKernel, if_pos hvd]
    have hb := truncatedSixthLower_region_bounds hd.le hvd.1
    have hz : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤ v.1*v.2*(1/2-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.1.le hb.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    have hp := profile_nonneg (clipped_nonneg n δ) (u v.1 v.2)
    have hl := clipped_profile_lower ht ht' hd hdt n hv
    exact div_le_div₀ (hp.trans hl) hl (StaircaseActual.denominator_pos hd.le hvd) hz
  · rw [uniform, if_neg hv]
    exact (truncatedSixthMass_kernels_bounds hd (by linarith) v).2.1

theorem clipped_Gamma_payment {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2) (n : ℕ) :
    Gamma (clipped n δ) t ≤ truncatedSixthLowerHadmdelta δ := by
  rw [Gamma, (truncatedSixthMass_literal_integrals hd (by linarith)).2]
  exact mul_le_mul_of_nonneg_left
    (integral_mono (uniform_integrable _ ht.le) (truncatedSixthMass_kernels_integrable hd (by linarith)).2
      (clipped_uniform_le_actual ht ht' hd hdt n)) (by norm_num)

/-- The actual h coefficient pays the entire finite iterate and its explicit two losses. -/
theorem finite_Gamma_payment {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2) (n : ℕ) :
    C n - loss (transferredLower n)*t - deltaLoss δ*E n ≤ truncatedSixthLowerHadmdelta δ := by
  have hpos := deltaLoss_nonneg hd (show δ ≤ 1/10 by linarith)
  have hw := (Gamma_loss (transferredLower_nonneg n) ht.le ht').2
  have hd' := (Gamma_loss (transferredDebit_nonneg n) ht.le ht').1
  have hm := mul_le_mul_of_nonneg_left (sub_nonneg.mp hd') hpos
  have hv := Gamma_mono (fun j => le_max_right 0
    (transferredLower n j - deltaLoss δ*transferredDebit n j)) ht.le
  rw [Gamma_sub_mul _ _ _ ht.le] at hv
  have hp := clipped_Gamma_payment ht ht' hd hdt n
  change Gamma (fun j => max 0 (transferredLower n j - deltaLoss δ*transferredDebit n j)) t ≤ _ at hp
  dsimp [C,E]
  linarith only [hw,hm,hv,hp]

/-- Arbitrary symbolic n; no table, margin, integral or counting premise. -/
theorem actual_count_lower (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerF6lin + C n - ε)*wuSingularSeries N*N/Real.log N^(2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
        ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
        ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  let B := loss (transferredLower n)
  have hB : 0 ≤ B := loss_nonneg _
  let t : ℝ := min (1/1000) (ε/(4*(B+1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht' : t ≤ 1/1000 := min_le_left _ _
  have htp : t ≤ ε/(4*(B+1)) := min_le_right _ _
  have hpayt : B*t < ε/4 := by
    have h := (le_div_iff₀ (show 0 < 4*(B+1) by positivity)).mp htp
    nlinarith only [h,ht]
  obtain ⟨a,ha,_,hc⟩ := truncatedSixthZeroDelta_actual_lower (half_pos hε)
  let d : ℝ := min a (min (t/2) (marginRadius (E n) (ε/4)))
  have hd : 0 < d := lt_min ha (lt_min (half_pos ht)
    (marginRadius_pos (E_nonneg n) (by positivity)))
  let δ : ℝ := d/2
  have hδ : 0 < δ := half_pos hd
  have hδd : δ < d := half_lt_self hd
  have hδa : δ < a := hδd.trans_le (min_le_left _ _)
  have hδt : δ ≤ t/2 := hδd.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ < marginRadius (E n) (ε/4) :=
    hδd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpayd := deltaLoss_mul_lt_margin (E_nonneg n) (show 0 < ε/4 by positivity) hδ hδr
  have hp := finite_Gamma_payment ht ht' hδ hδt n
  obtain ⟨T,hT,hN⟩ := hc δ hδ hδa
  refine ⟨max 512 T, le_max_left _ _, ?_⟩
  intro N hNT he
  have hTN : T ≤ N := (le_max_right _ _).trans hNT
  have hcoef : truncatedSixthLowerF6lin+C n-ε ≤
      truncatedSixthLowerF6lin+truncatedSixthLowerHadmdelta δ-ε/2 := by
    change C n-B*t-deltaLoss δ*E n ≤ _ at hp
    linarith only [hpayt,hpayd,hp]
  have hm := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hTN))
  have hm' : (truncatedSixthLowerF6lin+C n-ε)*wuSingularSeries N*N/Real.log N^(2 : ℕ) ≤
      (truncatedSixthLowerF6lin+truncatedSixthLowerHadmdelta δ-ε/2)*
        wuSingularSeries N*N/Real.log N^(2 : ℕ) := by
    simpa only [truncatedSixthMassScale,mul_div_assoc,mul_assoc] using hm
  exact hm'.trans (hN N hTN he)

end
end DirectFiniteF6
