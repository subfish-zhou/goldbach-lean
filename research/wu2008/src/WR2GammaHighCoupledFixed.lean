import WR2GammaHighCoupledSlack

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real
open scoped Classical

theorem actual_count_coupled_fixed {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      5*psiCount (row.castAdd 4) N ≤
        (classicalEight row + (2/(1-2*δ))*(omega3XIntegralEnvelope
          (Wu04RemainingCore.row row).kappa3 (Wu04RemainingCore.row row).kappa1 +
          SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row)) + ε)*theta row N δ+
          ε*truncatedSixthMassScale N := by
  let B := 2/(1-2*δ)
  have hB : 0 ≤ B := div_nonneg (by norm_num) (by linarith)
  have hcap : 0 ≤ SecondFunctionalCoupled.existenceCap := by norm_num [SecondFunctionalCoupled.existenceCap]
  obtain ⟨t,ht,hslack⟩ := Coupled.joint_slack (mul_nonneg hB hcap) (half_pos he)
  obtain ⟨T,hT,h⟩ := actual_count_coupled hd hh ht ht (half_pos he)
  refine ⟨T,hT,?_⟩
  intro N hN hn row
  let F := (1+t)*(1+t*exp (-eulerMascheroniConstant))*(1+t)
  have hF : 1 ≤ F := by
    calc
      (1:ℝ) = 1*1*1 := by norm_num
      _ ≤ F := by dsimp [F]; gcongr <;> nlinarith [mul_pos ht (exp_pos (-eulerMascheroniConstant))]
  have hsup := (SecondFunctionalCoupled.jointSup_bounds _ (row_analytic row).mother
    (row_analytic row).two_lt_s.le).2
  have hpay := (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsup hB) (sub_nonneg.mpr hF)).trans hslack
  have hc : F*B*SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row) ≤
      B*SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row)+ε/2 := by
    dsimp only [F,B] at hpay ⊢
    nlinarith only [hpay]
  have ha := h N hN hn row
  have htheta := theta_nonneg (N := N) row (by omega) hd hh
  have hs : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    exact div_nonneg (mul_nonneg (wuSingularSeries_pos N (by omega)).le (Nat.cast_nonneg _)) (sq_nonneg _)
  have hp := mul_le_mul_of_nonneg_right hc htheta
  have heS := mul_nonneg he.le hs
  dsimp only [F,B] at hp
  nlinarith only [ha,hp,heS]

end WuPaper.R2GammaHigh
#print axioms WuPaper.R2GammaHigh.actual_count_coupled_fixed
