import Wu04FullPsiLower

namespace Wu04ClassicalTelescope
open Wu2008DoubleSieve Real SecondFunctionalParameters
open Wu04FullPsiLower Wu04FullPsiSharp Wu04FullPsiEndpoints
noncomputable section

def ds : ℝ := d row1.S
def dk : ℝ := d row1.kappa1
def rationalPart : ℝ :=
  88971942442008073670136702578423/1122766184207112210284453021013300

/-- Only ratios of adjacent original primitive endpoints; the repeated 6/5 is collected. -/
def collected : ℝ := rationalPart +
  (4-ds)*log (6/5) + (6-ds-dk)*log (17/16) +
  (17/3-ds-dk)*log (190/153) + (23/3-ds-dk)*log (20/19) +
  (1/3-ds-dk)*log (253/200) + (1/3-ds)*log (254/253) -
  ds*log (177/127) - log (10/9)

/-- All original source gates and all collected signs are checked before payment. -/
theorem first_gates :
    2 < row1.s ∧ row1.s ≤ row1.S ∧ 2 ≤ row1.S*(1-1/row1.s) ∧
    2 < row1.kappa3 ∧ row1.kappa3 ≤ row1.kappa1 ∧
    2 ≤ row1.kappa1*(1-1/row1.kappa3) ∧
    3 ≤ row1.S ∧ 3 ≤ row1.kappa1 ∧ 2 < row1.kappa2 ∧ row1.kappa2 ≤ 3 :=
  original_classical_gates 0

theorem collected_signs :
    0 ≤ 4-ds ∧ 0 ≤ 6-ds-dk ∧ 0 ≤ 17/3-ds-dk ∧ 0 ≤ 23/3-ds-dk ∧
    1/3-ds-dk ≤ 0 ∧ 1/3-ds ≤ 0 ∧ 0 ≤ ds := by
  norm_num [ds,dk,d,row1]

private theorem log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    log (a/b) = log a-log b := log_div ha.ne' hb.ne'

/-- Exact endpoint cancellation of BOTH J and all THREE signed L terms. -/
theorem first_classical_telescope : classicalLower row1 = collected := by
  rw [classicalLower,
    lowerJ_closed (by norm_num [row1]) (by norm_num [row1]),
    lowerJ_closed (by norm_num [row1]) (by norm_num [row1]),
    upperL_closed (by norm_num [row1]), upperL_closed (by norm_num [row1])]
  have hj := log_ratio (by norm_num : (0:ℝ)<177/50) (by norm_num : (0:ℝ)<6/5)
  have hk := log_ratio (by norm_num : (0:ℝ)<253/100) (by norm_num : (0:ℝ)<36/25)
  have hl := log_ratio (by norm_num : (0:ℝ)<177/50) (by norm_num : (0:ℝ)<2)
  have hm := log_ratio (by norm_num : (0:ℝ)<253/100) (by norm_num : (0:ℝ)<2)
  have hn := log_ratio (by norm_num : (0:ℝ)<19/10) (by norm_num : (0:ℝ)<2)
  have hp := log_ratio (by norm_num : (0:ℝ)<10) (by norm_num : (0:ℝ)<9)
  have hq : log ((9:ℝ)/10) = -log (10/9) := by
    rw [show (9:ℝ)/10=(10/9)⁻¹ by norm_num, log_inv]
  have h1 := log_mul (by norm_num : (6:ℝ)/5 ≠ 0) (by norm_num : (6:ℝ)/5 ≠ 0)
  have h2 := log_ratio (by norm_num : (0:ℝ)<153/100) (by norm_num : (0:ℝ)<36/25)
  have h3 := log_ratio (by norm_num : (0:ℝ)<19/10) (by norm_num : (0:ℝ)<153/100)
  have h4 := log_ratio (by norm_num : (0:ℝ)<2) (by norm_num : (0:ℝ)<19/10)
  have h5 := log_ratio (by norm_num : (0:ℝ)<253/100) (by norm_num : (0:ℝ)<2)
  have h6 := log_ratio (by norm_num : (0:ℝ)<127/50) (by norm_num : (0:ℝ)<253/100)
  have h7 := log_ratio (by norm_num : (0:ℝ)<177/50) (by norm_num : (0:ℝ)<127/50)
  norm_num at hj hk hl hm hn h1 h2 h3 h4 h5 h6 h7
  norm_num [row1,c,d,Wu04FullPsiSharp.e,f,Wu04FullPsiClassical.lSmallUpper,
    collected,rationalPart,ds,dk]
  rw [hj,hk,hl,hm,hn,hq,h2,h3,h4,h6,h7,h1]
  ring

#print axioms first_classical_telescope
end
end Wu04ClassicalTelescope
