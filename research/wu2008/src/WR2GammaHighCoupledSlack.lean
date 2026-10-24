import WR2GammaHighCoupledAssembly

noncomputable section
namespace WuPaper.R2GammaHigh.Coupled
open Wu2008DoubleSieve Real

/-- A single positive tolerance pays both sieve and true-li perturbations. -/
theorem joint_slack {M ε : ℝ} (hM : 0 ≤ M) (he : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      ((1+t)*(1+t*exp (-eulerMascheroniConstant))*(1+t)-1)*M ≤ ε := by
  let E := exp (-eulerMascheroniConstant)
  let B := (3+4*E)*M
  have hE : 0 ≤ E := (exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg (by positivity) hM
  let t := min 1 (ε/(B+1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos he (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hbudget : t*B ≤ ε := by
    have hb := (le_div_iff₀ (show 0 < B+1 by linarith)).mp (min_le_right 1 (ε/(B+1)))
    change t*(B+1) ≤ ε at hb
    nlinarith
  have hsq : (1+t)^2 ≤ 1+3*t := by nlinarith
  have hpoly : (1+t)*(1+t*E)*(1+t) ≤ 1+(3+4*E)*t := by
    have hx := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 1+t*E by positivity)
    have htE := mul_le_mul_of_nonneg_right (show t*t ≤ t by nlinarith) hE
    nlinarith only [hx,htE]
  refine ⟨t,ht,?_⟩
  have hp := mul_le_mul_of_nonneg_right (sub_le_sub_right hpoly 1) hM
  dsimp only [B,E] at hbudget hp
  nlinarith only [hp,hbudget]

end WuPaper.R2GammaHigh.Coupled
#print axioms WuPaper.R2GammaHigh.Coupled.joint_slack
