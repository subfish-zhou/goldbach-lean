import F1JointCollected

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1SecondLogRecovery
namespace F1JointFTC

def commonA : ℝ := residueA+(1+secondFactorRatio)*partC
def commonAC : ℝ := residueA+residueC+(1+secondFactorRatio)*partC

/-- Collect the common logarithm before choosing its paying sign. -/
def jointMass : ℝ :=
  (1+residueB)*(log 2+log (3/2))+log (1127/600)+
  commonA*log (3884129/3606400)+commonAC*log (4508/2927)-
  residueB*log (2400/2381)+residueD*log (4508/3981)+rationalEndpointPart+
  (1+secondFactorRatio)*(partA*log (927/400)+partB*log (2254/1727)+
    (partF/2)*log quadraticRatio+((partG-8*partF)/(2*root))*log radicalRatio+rationalPart)+
  secondPayment+EJoint.payment

theorem jointMass_exact : jointMass = signedMainLogs+cPayment+EJoint.payment := by
  have hc : log ((1327:ℝ)/800)=log (3884129/3606400)+log (4508/2927) := by
    rw [← log_mul (by norm_num : (3884129:ℝ)/3606400 ≠ 0)
      (by norm_num : (4508:ℝ)/2927 ≠ 0)]
    norm_num
  unfold cPayment
  rw [collectedMass_exact]
  unfold jointMass signedMainLogs collectedMass commonA commonAC
  rw [hc]
  ring

theorem jointMass_le_actual : 8*jointMass ≤ Wu08TerminalAlignment.firstMain := by
  have hc := cPayment_le_actual
  have he := EJoint.payment_le
  rw [jointMass_exact,FirstActualRecovery.actual_first_recoveries,← finiteMainPayment_exact]
  unfold logRecovery
  linarith only [hc,he]

theorem common_signs : 0 ≤ commonA ∧ commonAC ≤ 0 := by
  norm_num [commonA,commonAC,residueA,residueC,secondFactorRatio,partC]

def low (x : ℝ) : ℝ := lowerLog x+lowerGapPayment x+F1LowerResidual.payment x
def high (x : ℝ) : ℝ := JointLogTotalComparison.V x-upperGapPayment x

theorem low_le_log {x : ℝ} (hx : 1 ≤ x) : low x ≤ log x := by
  have h := F1LowerResidual.payment_le hx
  unfold low
  linarith only [h]

theorem log_le_high {x : ℝ} (hx : 1 ≤ x) : log x ≤ high x := by
  have h := upperGapPayment_le hx
  unfold high
  linarith only [h]

/-- A single existing-envelope payment for the fully collected log expression. -/
def jointLower : ℝ :=
  (1+residueB)*((JointLogTotalComparison.V 2-upperTwoPayment)+high (3/2))+low (1127/600)+
  commonA*low (3884129/3606400)+commonAC*high (4508/2927)-
  residueB*low (2400/2381)+residueD*high (4508/3981)+rationalEndpointPart+
  (1+secondFactorRatio)*(partA*high (927/400)+partB*low (2254/1727)+
    (partF/2)*high quadraticRatio+((partG-8*partF)/(2*root))*low radicalRatio+rationalPart)+
  secondPayment+EJoint.payment

theorem jointLower_le_jointMass : jointLower ≤ jointMass := by
  obtain ⟨_,_,hb,hb1,hd⟩ := residue_signs
  obtain ⟨ha,hac⟩ := common_signs
  have htwo : log 2 ≤ JointLogTotalComparison.V 2-upperTwoPayment := by
    linarith only [upperTwoPayment_le]
  have h0 := mul_le_mul_of_nonpos_left
    (add_le_add htwo (log_le_high (by norm_num : (1:ℝ) ≤ 3/2))) hb1
  have h1 := low_le_log (by norm_num : (1:ℝ) ≤ 1127/600)
  have h2 := mul_le_mul_of_nonneg_left (low_le_log (by norm_num : (1:ℝ) ≤ 3884129/3606400)) ha
  have h3 := mul_le_mul_of_nonpos_left (log_le_high (by norm_num : (1:ℝ) ≤ 4508/2927)) hac
  have h4 := mul_le_mul_of_nonpos_left (low_le_log (by norm_num : (1:ℝ) ≤ 2400/2381)) hb
  have h5 := mul_le_mul_of_nonpos_left (log_le_high (by norm_num : (1:ℝ) ≤ 4508/3981)) hd
  have h6 := mul_le_mul_of_nonpos_left (log_le_high (by norm_num : (1:ℝ) ≤ 927/400))
    (show partA ≤ 0 by norm_num [partA])
  have h7 := mul_le_mul_of_nonneg_left (low_le_log (by norm_num : (1:ℝ) ≤ 2254/1727))
    (show 0 ≤ partB by norm_num [partB])
  have h8 := mul_le_mul_of_nonpos_left
    (log_le_high (show 1 ≤ quadraticRatio by norm_num [quadraticRatio]))
    (show partF/2 ≤ 0 by norm_num [partF])
  have h9 := mul_le_mul_of_nonneg_left (low_le_log radicalRatio_ge_one)
    (show 0 ≤ (partG-8*partF)/(2*root) by
      apply div_nonneg
      · norm_num [partG,partF]
      · exact mul_nonneg (by norm_num) root_pos.le)
  have hinner := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h6 h7) h8) h9)
    (show 0 ≤ 1+secondFactorRatio by linarith only [secondFactorRatio_pos])
  unfold jointLower jointMass
  linarith only [h0,h1,h2,h3,h4,h5,hinner]

theorem jointLower_le_actual : 8*jointLower ≤ Wu08TerminalAlignment.firstMain := by
  linarith only [jointLower_le_jointMass,jointMass_le_actual]

end F1JointFTC
