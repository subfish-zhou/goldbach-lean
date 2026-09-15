import Wu04MainCollection

namespace Wu04MainPayment
open Wu2008DoubleSieve Real SecondFunctionalParameters SharpLogRecurrence JointLogTotalComparison
open Wu04MainClassical Wu04MainCollection Wu04MainProducer
open Wu04FullPsiCostCertificate Wu04MainTail
noncomputable section

def pS : List ℝ := [454/353,353/290,145/122,61/55]
def pK : List ℝ := [353/290,145/122]
def qS : List ℝ := [6/5,17/16,190/153,20/19,253/200,254/253,177/127]
def qK : List ℝ := [17/16,190/153,20/19,253/200]
def lS : List ℝ := [6/5,6/5,17/16,190/153,20/19,253/200,254/253]
def lK : List ℝ := [6/5,6/5,17/16]
def uS : List ℝ := [253/200,254/253,177/127]
def uK : List ℝ := [253/200]

def jSPaid : ℝ := paidJ row1.s row1.S (pay pS) (pay qS)
def jKPaid : ℝ := paidJ row1.kappa3 row1.kappa1 (pay pK) (pay qK)
def lSPaid : ℝ := lRest row1.S-(1/10)*pay lS+(28/15)*upperPay uS
def lKPaid : ℝ := lRest row1.kappa1-(1/10)*pay lK+(28/15)*upperPay uK

def classicalPaid : ℝ := jSPaid+jKPaid-2*lSPaid-2*lKPaid+
  2*lowerLog (20/19)-V (10/9)

theorem jS_payment : jSPaid ≤ lowerJ row1.s row1.S := by
  have hp := lower_product pS (by norm_num [pS])
  have hq := lower_product qS (by norm_num [qS])
  have hp' : pS.prod = row1.S/row1.s := by norm_num [pS,row1]
  have hq' : qS.prod = (row1.S-1)/(row1.s-1) := by norm_num [qS,row1]
  rw [hp'] at hp
  rw [hq'] at hq
  apply paid_j (by norm_num [row1]) (by norm_num [row1])
    (by norm_num [a,row1]) (by norm_num [c,b,a,row1])
    (by norm_num [Wu04MainClassical.e,d,b,a,row1])
    (by norm_num [ratio,yl,yu,b,a,row1]) (by norm_num [yu,yl,b,a,row1]) hp.2 hq.2 hq.1

theorem jK_payment : jKPaid ≤ lowerJ row1.kappa3 row1.kappa1 := by
  have hp := lower_product pK (by norm_num [pK])
  have hq := lower_product qK (by norm_num [qK])
  have hp' : pK.prod = row1.kappa1/row1.kappa3 := by norm_num [pK,row1]
  have hq' : qK.prod = (row1.kappa1-1)/(row1.kappa3-1) := by norm_num [qK,row1]
  rw [hp'] at hp
  rw [hq'] at hq
  apply paid_j (by norm_num [row1]) (by norm_num [row1])
    (by norm_num [a,row1]) (by norm_num [c,b,a,row1])
    (by norm_num [Wu04MainClassical.e,d,b,a,row1])
    (by norm_num [ratio,yl,yu,b,a,row1]) (by norm_num [yu,yl,b,a,row1]) hp.2 hq.2 hq.1

theorem lS_payment : upperL row1.S ≤ lSPaid := by
  have hl := (lower_product lS (by norm_num [lS])).2
  have hu := upper_product uS (by norm_num [uS])
  have hl' : lS.prod = row1.S-2 := by norm_num [lS,row1]
  have hu' : uS.prod = (row1.S-1)/2 := by norm_num [uS,row1]
  rw [hl'] at hl
  rw [hu'] at hu
  rw [collect_l (by norm_num [row1])]
  unfold lSPaid
  linarith only [hl,hu]

theorem lK_payment : upperL row1.kappa1 ≤ lKPaid := by
  have hl := (lower_product lK (by norm_num [lK])).2
  have hu := upper_product uK (by norm_num [uK])
  have hl' : lK.prod = row1.kappa1-2 := by norm_num [lK,row1]
  have hu' : uK.prod = (row1.kappa1-1)/2 := by norm_num [uK,row1]
  rw [hl'] at hl
  rw [hu'] at hu
  rw [collect_l (by norm_num [row1])]
  unfold lKPaid
  linarith only [hl,hu]

/-- Both new FTC producers are consumed in the full original signed classical numerator. -/
theorem classical_payment : classicalPaid ≤ Wu08OriginalPsiRecovery.classicalNumerator row1 := by
  have hj := (jS_payment.trans (lower_j (by norm_num [row1]) (by norm_num [row1]) (by norm_num [a,row1])))
  have hk := (jK_payment.trans (lower_j (by norm_num [row1]) (by norm_num [row1]) (by norm_num [a,row1])))
  have hl := (upper_l (by norm_num [row1] : 3≤row1.S)).trans lS_payment
  have hm := (upper_l (by norm_num [row1] : 3≤row1.kappa1)).trans lK_payment
  have hn := (Wu04FullPsiClassical.l_small_upper (by norm_num [row1] : 2<row1.kappa2)
    (by norm_num [row1])).trans Wu04FullPsiLower.first_small_L_bound
  unfold classicalPaid Wu08OriginalPsiRecovery.classicalNumerator
  linarith only [hj,hk,hl,hm,hn]

theorem classical_rational : (239103:ℝ)/1000000 ≤ classicalPaid := by
  norm_num [classicalPaid,jSPaid,jKPaid,lSPaid,lKPaid,paidJ,lRest,ratio,rest,yl,yu,
    c,Wu04MainClassical.e,h2,h3,d,b,a,pay,upperPay,pS,pK,qS,qK,lS,lK,uS,uK,row1,lowerLog,upperLog,V]

theorem cost_rational : rationalCap ≤ (80370:ℝ)/1000000 := by
  norm_num [rationalCap,cap,tripleCap,fourCap,lx,ux,ly,uy,lz,uz,lw,uw,V,lowerLog,upperLog]

#print axioms classical_payment
#print axioms classical_rational
#print axioms cost_rational
end
end Wu04MainPayment
