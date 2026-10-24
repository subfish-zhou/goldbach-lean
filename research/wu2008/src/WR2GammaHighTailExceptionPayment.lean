import WR2GammaHighTailExceptions

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighBoxRecovery Real Filter
open scoped Topology

theorem square_error_paid {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (max 1 (1/highEta))^6*N*(1+log N)/((N : ℝ)^highEta-1) ≤ ε*truncatedSixthMassScale N := by
  have hK : 0 < 4*(max 1 (1/highEta))^6 := by positivity
  obtain ⟨T0,hT0,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 1 he hK
    (show 0 < highEta by norm_num [highEta])
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : 0 < highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ)))
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 T2),by omega,fun N hN => ?_⟩
  have hy := h1 N (by omega)
  have hl := h2 N (by omega)
  dsimp only [Function.comp_apply] at hy hl
  have hden : 1/((N : ℝ)^highEta-1) ≤ 2/(N : ℝ)^highEta := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    linarith
  calc
    _ = (max 1 (1/highEta))^6*N*(1+log N)*(1/((N : ℝ)^highEta-1)) := by ring
    _ ≤ (max 1 (1/highEta))^6*N*(1+log N)*(2/(N : ℝ)^highEta) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ (max 1 (1/highEta))^6*N*(2*log N)*(2/(N : ℝ)^highEta) := by gcongr; linarith
    _ = (4*(max 1 (1/highEta))^6)*N*log N^(1 : ℕ)/(N : ℝ)^highEta := by ring
    _ ≤ _ := hp N (by omega)

theorem bad_error_paid {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (max 1 (1/highEta))^7*log N/log 2 ≤ ε*truncatedSixthMassScale N := by
  have hK : 0 < (max 1 (1/highEta))^7/log 2 := by positivity
  obtain ⟨T,hT,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 1 he hK
    (by norm_num : (0 : ℝ)<1/2)
  refine ⟨T,hT,fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hy : (N : ℝ)^(1/2 : ℝ) ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/2 : ℝ) ≤ 1)
  have hdiv : 1 ≤ (N : ℝ)/(N : ℝ)^(1/2 : ℝ) :=
    (le_div_iff₀ (rpow_pos_of_pos hn _)).mpr (by simpa using hy)
  have hm := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ ((max 1 (1/highEta))^7/log 2)*log N by positivity)
  have hb := hp N hN
  norm_num only [pow_one, mul_one] at hm hb
  ring_nf at hm hb ⊢
  linarith only [hm,hb]

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.square_error_paid
#print axioms WuPaper.R2GammaHigh.Tail.bad_error_paid
