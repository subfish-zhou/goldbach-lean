import HighBoxRecoveryJointPayment

namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Genuine Theta normalization from actual support, without a source box. -/
theorem theta_from_actual_support {i N : ℕ} {δ η : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime)
    (hsize : ∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) :
    2*liuUniversalProduct*N/log N^2 * boxConvolutionReciprocalMass W ≤
      boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  apply boxTheta_lower_of_support W hN
  · intro d hd
    exact boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
  · intro d hd
    have hdpos := boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
    have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hdQ : (d : ℝ) < (N : ℝ)^(1/2-δ) :=
      (hsize d hd).trans_lt (rpow_lt_rpow_of_exponent_lt hN1 (by linarith))
    refine ⟨(one_lt_div hdr).mpr hdQ, ?_⟩
    apply (div_le_self (by positivity) hd1).trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1.le
      (show (1/2 : ℝ)-δ ≤ 1 by linarith)

/-- Full R1+R2 paid against the true li/singular-series Theta, uniformly before
all shrinking prime boxes of depth at most three. No improvement is assumed. -/
theorem remainders_relative {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, i ≤ 3 → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin i → ℝ, (∀ j, (N : ℝ)^η ≤ V j) → (∀ j, V j ≤ N) →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      omega3SieveR1 N (⌊Q⌋₊+1) δ s t (sqrt Q) W +
        omega3SieveR2 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤ ε*boxTheta N Q W := by
  obtain ⟨C,hC,T1,hT14,hR1⟩ := R1_total_slack 3 hδ hη (show (0 : ℝ) < 18 by norm_num)
  obtain ⟨K,hK,hR2⟩ := R2_total_slack 3 hδ hδhalf hη
  obtain ⟨T2,hmass⟩ := wu_boxConvolution_mass_bounds 3 hη
  let c : ℝ := 2*liuUniversalProduct*(1/12 : ℝ)^3
  let F : ℝ := (max 1 (1/η))^(3+2)
  let P : ℝ := 2*K*F/log 2
  have hc : 0 < c := by dsimp [c]; have := liuUniversalProduct_pos; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have he : 0 < ε/2*c := by positivity
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3,hlogBudget⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (max 1 (C/(ε/2*c)))))
  obtain ⟨T4,hpowBudget⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 22 (show 0 < P/(ε/2*c) by positivity) hη)
  refine ⟨max T1 (max T2 (max T3 T4)),hT14.trans (le_max_left _ _),?_⟩
  intro N hN i hi Δ hlo hhi V hV hVN hW hsize s t hs hst ht W Q
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_left T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hN4 := (le_max_right T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hNfour := hT14.trans hN1
  have hlog1 : 1 ≤ log (N : ℝ) := (le_max_left _ _).trans (hlogBudget N hN3)
  have hlog : 0 < log (N : ℝ) := by linarith
  have htheta : c*N/log N^17 ≤ boxTheta N Q W := by
    have hm := (hmass N hN2 i hi Δ hlo hhi V hV hVN).1
    have hprod := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 2*liuUniversalProduct*N/log N^2 by have := liuUniversalProduct_pos; positivity)
    have ht' := theta_from_actual_support W hNfour hδ.le hη (fun j p hp => (hW j p hp).1) hsize
    calc
      _ = 2*liuUniversalProduct*N/log N^2 * ((1/12 : ℝ)^3/log N^(5*3)) := by dsimp [c]; ring
      _ ≤ _ := hprod.trans ht'
  have hb1 : omega3SieveR1 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤ ε/2*boxTheta N Q W := by
    have hr := hR1 N hN1 i hi W hW hsize s t hs hst ht (sqrt Q)
    have hbudget : C/log N ≤ ε/2*c := by
      apply (div_le_iff₀ hlog).mpr
      have hb := (div_le_iff₀ he).mp ((le_max_right _ _).trans (hlogBudget N hN3))
      nlinarith
    calc
      _ ≤ C*N/log (N : ℝ)^(18 : ℝ) := hr
      _ = (C/log N)*((N : ℝ)/log N^17) := by norm_num; ring
      _ ≤ (ε/2*c)*((N : ℝ)/log N^17) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = ε/2*(c*N/log N^17) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htheta (by positivity)
  have hb2 : omega3SieveR2 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤ ε/2*boxTheta N Q W := by
    have hr := hR2 N hNfour i hi W hW hsize s t hs hst ht
    calc
      _ ≤ K*F*N*((1+log N)*log N^4/((N : ℝ)^η*log 2)) := hr
      _ ≤ K*F*N*((2*log N)*log N^4/((N : ℝ)^η*log 2)) := by gcongr; linarith
      _ = P*N*log N^5/(N : ℝ)^η := by dsimp [P]; ring
      _ ≤ P*N*log N^5/((P/(ε/2*c))*log N^22) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (hpowBudget N hN4)
      _ = ε/2*(c*N/log N^17) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left htheta (by positivity)
  linarith

end
end HighBoxRecovery
