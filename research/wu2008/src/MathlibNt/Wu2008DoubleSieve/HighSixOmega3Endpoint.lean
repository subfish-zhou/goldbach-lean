import MathlibNt.Wu2008DoubleSieve.HighSixOmega3ActualX

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter
open scoped Classical Topology

/-- Full singular-series normalization for the actual high-prime support. -/
theorem theta_lower_singular {N : ℕ} {δ : ℝ} (hN : 4 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    2*wuSingularSeries N*(N : ℝ)/log N^2*boxConvolutionReciprocalMass (W N) ≤ B6 N δ := by
  apply boxTheta_lower_singular_of_support (W N) hN (fun _ hp => support_pos hp)
  intro p hp
  have hg := support_geometry (by omega) hδ hδhi ((support N) ▸ hp)
  exact ⟨hg.2.2.2.1,hg.2.2.2.2.1⟩

/-- Actual X-to-integral payment includes the density and the full 480 mass. -/
theorem actualX_scaled_paid {δ K ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hK : 0 < K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      omega3SieveX N δ s S (W N)*(K*wuSingularSeries N/log N) ≤
        omega3XIntegralMain N δ s S (W N)*(K*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := actualX_integral_paid hδ hδhi
    (show 0 < ε/(240*K) by positivity)
  obtain ⟨T2,_,hT2⟩ := B6_total_mass hδ hδhi
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := by omega
  have hC := wuSingularSeries_pos N (by omega)
  have hl := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hr := mul_le_mul_of_nonneg_right (hT1 N (by omega))
    (show 0 ≤ K*wuSingularSeries N/log N by positivity)
  have ht := mul_le_mul_of_nonneg_left (theta_lower_singular hN4 hδ hδhi)
    (show 0 ≤ ε/480 by positivity)
  have hm := mul_le_mul_of_nonneg_left (hT2 N (by omega) he).2
    (show 0 ≤ ε/480 by positivity)
  have hc : (ε/(240*K)*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N))*
      (K*wuSingularSeries N/log N) =
      (ε/480)*(2*wuSingularSeries N*(N : ℝ)/log N^2*boxConvolutionReciprocalMass (W N)) := by
    field_simp
    ring
  rw [add_mul,hc] at hr
  linarith

/-- Both physical remainders have been paid before evaluating actual X. -/
theorem O3_X_only {δ ρ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O3 N δ ≤ omega3SieveX N δ s S (W N)*
        (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ)))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := O3_actualX_paid hδ hδhi hρ (show 0 < ε/3 by positivity)
  obtain ⟨T2,_,hT2⟩ := R1_paid hδ hδhi (show 0 < ε/3 by positivity)
  obtain ⟨T3,_,hT3⟩ := R2_paid hδ hδhi (show 0 < ε/3 by positivity)
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have h1 := hT1 N (by omega) he
  have h2 := hT2 N (by omega) (sqrt ((N : ℝ)^(1/2-δ)))
  have h3 := hT3 N (by omega)
  linarith

/-- A fully paid intermediate endpoint with explicit fixed slack. -/
theorem O3_integral_slack {δ ρ τ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O3 N δ ≤ ((1+τ)*((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ)))/4*
        omega3XIntegralEnvelope s S)*B6 N δ+ε*truncatedSixthMassScale N := by
  have hK := omega3X_fixed_density_factor_pos (show δ < 1/2 by linarith) hρ
  obtain ⟨T1,hT14,hT1⟩ := O3_X_only hδ hδhi hρ (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := actualX_scaled_paid hδ hδhi hK (half_pos hε)
  obtain ⟨T3,_,hT3⟩ := integral_scaled hδ hδhi hK.le hτ
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have h1 := hT1 N (by omega) he
  have h2 := hT2 N (by omega) he
  have h3 := hT3 N (by omega)
  linarith

/-- Choose both analytic slacks internally, before every threshold and label. -/
theorem density_slack_choice {δ ε : ℝ} (hε : 0 < ε) :
    ∃ ρ τ : ℝ, 0 < ρ ∧ 0 < τ ∧
      (1+τ)*((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ)))/4*
        omega3XIntegralEnvelope s S ≤
      (2/(1-2*δ))*omega3XIntegralEnvelope s S+ε := by
  let f : ℝ → ℝ := fun r =>
    (1+r)*((1+r)*(1+r*exp (-eulerMascheroniConstant))*(8/(1-2*δ)))/4*
      omega3XIntegralEnvelope s S
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
  obtain ⟨r,hr,hbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  have hdist : dist (r/2) (0 : ℝ) < r := by
    rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)]
    linarith
  have hb := (abs_lt.mp (show |f (r/2)-f 0| < ε by
    simpa only [Real.dist_eq] using hbound hdist)).2
  refine ⟨r/2,r/2,half_pos hr,half_pos hr,?_⟩
  have hf0 : f 0 = (2/(1-2*δ))*omega3XIntegralEnvelope s S := by dsimp [f]; ring
  rw [hf0] at hb
  change f (r/2) ≤ _
  linarith

/-- The original O3 integral terminal, with the fixed-delta factor retained. -/
theorem O3_integral_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O3 N δ ≤ (2/(1-2*δ))*omega3XIntegralEnvelope s S*B6 N δ+
        ε*truncatedSixthMassScale N := by
  obtain ⟨ρ,τ,hρ,hτ,hslack⟩ := density_slack_choice (δ := δ) (show 0 < ε/960 by positivity)
  obtain ⟨T1,hT14,hT1⟩ := O3_integral_slack hδ hδhi hρ hτ (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := B6_total_mass hδ hδhi
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have h1 := hT1 N (by omega) he
  have hm := hT2 N (by omega) he
  have hs := mul_le_mul_of_nonneg_right hslack hm.1
  have hp := mul_le_mul_of_nonneg_left hm.2 (show 0 ≤ ε/960 by positivity)
  nlinarith

/-- Consume the proved negative integral on the same threshold, leaving O1. -/
theorem count_integral_upper_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*C6 N ≤ O1 N δ-J*B6 N δ+
        (2/(1-2*δ))*omega3XIntegralEnvelope s S*B6 N δ+ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := count_integral_paid hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := O3_integral_paid hδ hδhi (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have h1 := hT1 N (by omega) he
  have h2 := hT2 N (by omega) he
  linarith

end Wu2008DoubleSieve.HighSix.Omega3Upper
