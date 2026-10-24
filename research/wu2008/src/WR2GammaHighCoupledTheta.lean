import WR2GammaHighCoupledNormalization

noncomputable section
namespace WuPaper.R2GammaHigh.Coupled
open Wu2008DoubleSieve HighUnitSource HighUnit Real Finset
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

theorem integralMass_joint_theta {N : ℕ} {δ τ : ℝ} (row : Fin 3)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (ht : 0 ≤ τ)
    (hli : (N:ℝ)/log N ≤ (1+τ)*logarithmicIntegral N) :
    wuSingularSeries N/log N*integralMass row N δ ≤
      (SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row)*(1+τ)/4)*theta row N δ := by
  have hC : 0 ≤ wuSingularSeries N/log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hS := (SecondFunctionalCoupled.jointSup_bounds _ (row_analytic row).mother
    (row_analytic row).two_lt_s.le).1
  have ha := mul_le_mul_of_nonneg_left (integralMass_le_jointSup (N := N) row (by omega) hd hh) hC
  have heq : (∑ d ∈ boxConvolutionSupport (windows row N),
      (convolutionCoeff (windows row N) d : ℝ)*((N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d)))) =
      unitLogMass N δ (windows row N) := by
    unfold unitLogMass
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  rw [heq] at ha
  have hb := mul_le_mul_of_nonneg_right
    (unitLogMass_theta_comparison row hN hd hh ht hli) hS
  change (wuSingularSeries N/log N*unitLogMass N δ (windows row N))*_ ≤
    ((1+τ)/4*theta row N δ)*_ at hb
  calc
    _ ≤ wuSingularSeries N/log N*(unitLogMass N δ (windows row N)*
        SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row)) := ha
    _ = (wuSingularSeries N/log N*unitLogMass N δ (windows row N))*
        SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row) := by ring
    _ ≤ _ := hb
    _ = _ := by ring

/-- One threshold, with the original true logarithmic integral and joint supremum. -/
theorem actual_twelve_joint_theta {δ ρ τ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (ht : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      (∑ k : Fin 6, gamma row N δ (10+k.val)) +
        (∑ k : Fin 4, gamma row N δ (16+k.val)) +
        (gamma row N δ 20 + gamma row N δ 21) ≤
      ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(1+τ)*(2/(1-2*δ))*
        SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row))*theta row N δ+
        ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT1,h1⟩ := actual_twelve_integral_paid hd hh hr he
  obtain ⟨T2,_,h2⟩ := trueLi_near_one ht
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN hn row
  have ha := h1 N (by omega) hn row
  have hb := integralMass_joint_theta row (by omega) hd hh ht.le (h2 N (by omega))
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by linarith) (by positivity))
    (div_nonneg (by norm_num) (by linarith))
  have hc := mul_le_mul_of_nonneg_left hb hA
  have heq : integralMass row N δ * (A*wuSingularSeries N/log N) =
      A*(wuSingularSeries N/log N*integralMass row N δ) := by ring
  change _ ≤ integralMass row N δ*(A*wuSingularSeries N/log N)+_ at ha
  rw [heq] at ha
  apply ha.trans
  apply add_le_add _ le_rfl
  exact hc.trans_eq (by dsimp [A]; ring)

end WuPaper.R2GammaHigh.Coupled
#print axioms WuPaper.R2GammaHigh.Coupled.actual_twelve_joint_theta
