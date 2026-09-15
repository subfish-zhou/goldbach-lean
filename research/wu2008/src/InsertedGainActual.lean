import InsertedGainMass

namespace InsertedGain
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
noncomputable section

/-- The fixed analytic gain is now consumed on every actual once-inserted box.
Both its strict positive mass and the remaining arbitrary logarithmic error
are paid uniformly before the moving insertion endpoint. -/
theorem inserted_upper {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ (Fin.cons U V)) (29/10) ≤
        (wuUpperCoefficient (29/10)-1/10000)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ (Fin.cons U V)) (29/10) <
        wuUpperCoefficient (29/10)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have hη : 0 < highEta := by norm_num [highEta]
  have hd : δ ≤ 1/10 := by norm_num [highEta] at hδhi; linarith
  obtain ⟨C,_,T0,hT04,hmother⟩ := InsertedO2.inserted_log_integral_mother
    hδ hδhi ActualLogGain.rho_bounds.1 (by norm_num : (0 : ℝ) < 1/100)
    (by norm_num : (0 : ℝ) < 1/40000)
  obtain ⟨T1,_,hpay⟩ := supported_remainder_relative C hδ.le hη
    (by norm_num : (0 : ℝ) < 1/40000)
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hr U hU
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN4 := hT04.trans hN0
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have hg := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hU
  have hend := inserted_endpoints (show 2 ≤ N by omega) hδ.le hδhi hΔ hΔhi hV hr hU
  obtain ⟨hθ,hrem⟩ := hpay N hN1 Δ hlo hhi 3 le_rfl (Fin.cons U V) hend.1 hend.2
    (fun j p hp => (hg.1 j p hp).1) hg.2
  have hm := hmother N hN0 he Δ hlo hhi V hV hr U hU (29/10) (31/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hc := mul_le_mul_of_nonneg_right
    (ActualLogGain.coefficient_gain hd ActualLogGain.rho_bounds.1.le
      ActualLogGain.rho_bounds.2.1 ActualLogGain.rho_bounds.2.2
      (by norm_num : (0 : ℝ) ≤ 1/100) le_rfl) hθ.le
  have hu : wuBoxPhi N δ (convolutionWuWindows N Δ (Fin.cons U V)) (29/10) ≤
      (wuUpperCoefficient (29/10)-1/10000)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) := by
    nlinarith only [hm,hrem,hc]
  refine ⟨hθ,hu,?_⟩
  nlinarith only [hu,hθ]

end
end InsertedGain
