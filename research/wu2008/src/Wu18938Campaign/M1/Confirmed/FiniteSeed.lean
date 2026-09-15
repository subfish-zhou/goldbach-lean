import Wu18938Campaign.M1.Confirmed.LowerProfile
import Wu18938Campaign.M1.Confirmed.ClassicalExtended
import MathlibNt.Wu2008DoubleSieve.HighSixPhase7Feedback

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical Interval

theorem omega3_envelope {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    HighSourcePayload.theta N δ Δ V (fun d => omega3XIntegral s t (omega3XPhi N d δ)) ≤
      omega3XIntegralEnvelope s t *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  apply (roughBox_payload_theta_bounds hb hN hη hδ _ _).2
  intro d hd
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hh := roughBox_log_geometry hb (by omega) hη hδ hd
    linarith [hh.2.2.1]
  exact ⟨omega3XIntegral_nonneg hs hst ht hphi,omega3XIntegral_le_envelope hs hst ht hphi⟩

theorem first_classical_update (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 4 → 2 ≤ t - t / s →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (wuUpperCoefficient s - firstFunctionalGainPsi δ s t + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_first_integral m hη hδ hδhi (half_pos he)
  obtain ⟨T1,_,h1⟩ := classical_omega2 m hη hδ (half_pos he)
  obtain ⟨T2,_,h2⟩ := roughBox_upper_leaf_four m hη hδ (half_pos he)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht4 hratio
  have ha := h0 N (by omega) heven i Δ V hb s t hs hst (by linarith)
  have hb' := h1 N (by omega) heven i Δ V hb s t hs hst ht (by linarith) hratio
  have hc := h2 N (by omega) heven i Δ V hb t (by linarith) ht4
  have henv := mul_le_mul_of_nonneg_left
    (omega3_envelope hb (by omega) hη hδ hs hst (by linarith))
    (show 0 ≤ 2 / (1 - 2 * δ) by exact div_nonneg (by norm_num) (by linarith))
  have henv' : (2 / (1 - 2 * δ)) *
      HighSourcePayload.theta N δ Δ V (fun d => omega3XIntegral s t (omega3XPhi N d δ)) ≤
      2 * (omega3XIntegralEnvelope s t / (1 - 2 * δ)) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ 2 / (1 - 2 * δ) * (omega3XIntegralEnvelope s t *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) := henv
      _ = _ := by ring
  unfold firstFunctionalGainPsi
  nlinarith only [ha,hb',hc,henv']

theorem seed_upper (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 13 / 5 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (1 - HighSixPhase7.seed + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := first_classical_update m hη hδ (by linarith) he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb s hs hs26
  have hbase := hT N hN heven i Δ V hb (13 / 5) (179 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha : wuUpperCoefficient (13 / 5) = 1 :=
    jr1965F_normalized_initial (by norm_num) (by norm_num)
  rw [ha] at hbase
  have hgain := HighSixPhase7.psi_delta_lower hδ hδhi
  have hpay := mul_le_mul_of_nonneg_right
    (show 1 - firstFunctionalGainPsi δ (13 / 5) (179 / 50) + ε ≤
      1 - HighSixPhase7.seed + ε by linarith) (theta_nonneg hb (by omega) hη hδ)
  apply le_trans _ (hbase.trans hpay)
  unfold wuBoxPhi convolutionSieveCount
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact gamma5Classical_source_count_antitone N d (d * N)
    (hb.cutoff_antitone (by omega) hη hδ hd (by linarith) hs26)

end Wu18938Campaign.M1.Confirmed.Rebox
