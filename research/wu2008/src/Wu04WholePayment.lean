import Wu04WholeCollection

namespace Wu04WholePayment
open Wu2008DoubleSieve Real SharpLogRecurrence JointLogTotalComparison SecondFunctionalParameters
open Wu04FactorEnvelopes Wu04FactorJPrimitive Wu04WholeCollection
noncomputable section

def paidJ (B A p q : ℝ) : ℝ :=
  let a := Wu04MainClassical.a B A
  paid B A 1 (-4*a) A (3*a-1) p+
    paid B A (1/3) (-4*a/3) (3*A) (a-3) p+lower a*q

theorem collect_j {B A : ℝ} (hB : 1<B) (hA : 1<A)
    (hl1 : 0<yl B A (3*Wu04MainClassical.a B A-1))
    (hu1 : 0<yu A A (3*Wu04MainClassical.a B A-1))
    (hl2 : 0<yl B (3*A) (Wu04MainClassical.a B A-3))
    (hu2 : 0<yu A (3*A) (Wu04MainClassical.a B A-3)) :
    lowerJ B A=collected B A 1 (-4*Wu04MainClassical.a B A) A (3*Wu04MainClassical.a B A-1)+
      collected B A (1/3) (-4*Wu04MainClassical.a B A/3) (3*A) (Wu04MainClassical.a B A-3)+
      log (Wu04MainClassical.a B A)*log ((A-1)/(B-1)) := by
  rw [← collect hB hA hl1 hu1,← collect hB hA hl2 hu2,(logs hB hA).2,(logs hB hA).1]
  unfold lowerJ primitive
  ring

theorem pay_j {B A p q : ℝ} (hB : 1<B) (hA : 1<A) (ha : 1≤Wu04MainClassical.a B A)
    (hl1 : 0<yl B A (3*Wu04MainClassical.a B A-1))
    (hu1 : 0<yu A A (3*Wu04MainClassical.a B A-1))
    (hl2 : 0<yl B (3*A) (Wu04MainClassical.a B A-3))
    (hu2 : 0<yu A (3*A) (Wu04MainClassical.a B A-3))
    (hc1 : 0≤c1 1 (-4*Wu04MainClassical.a B A) A (3*Wu04MainClassical.a B A-1))
    (hc2 : 0≤c1 (1/3) (-4*Wu04MainClassical.a B A/3) (3*A) (Wu04MainClassical.a B A-3))
    (hp : p≤log (A/B)) (hq : q≤log ((A-1)/(B-1))) (hq0 : 0≤q) :
    paidJ B A p q≤lowerJ B A := by
  have htB : 0<1-1/B := sub_pos.mpr (by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hB)
  have htA : 0<1-1/A := sub_pos.mpr (by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hA)
  have hr1 : 0<ratio B A A (3*Wu04MainClassical.a B A-1) :=
    div_pos (mul_pos htA hl1) (mul_pos htB hu1)
  have hr2 : 0<ratio B A (3*A) (Wu04MainClassical.a B A-3) :=
    div_pos (mul_pos htA hl2) (mul_pos htB hu2)
  have h1 := paid_bound hr1 (div_pos hu1 hl1) hc1 hp
  have h2 := paid_bound hr2 (div_pos hu2 hl2) hc2 hp
  have h3 := mul_le_mul (lower_le_log ha) hq hq0 (log_nonneg ha)
  rw [collect_j hB hA hl1 hu1 hl2 hu2]
  exact add_le_add (add_le_add h1 h2) h3

def jSPaid : ℝ := paidJ row1.s row1.S (pay Wu04MainPayment.pS) (pay Wu04MainPayment.qS)
def jKPaid : ℝ := paidJ row1.kappa3 row1.kappa1 (pay Wu04MainPayment.pK) (pay Wu04MainPayment.qK)

theorem jS_payment : jSPaid≤lowerJ row1.s row1.S := by
  have hp := product_bounds Wu04MainPayment.pS (by norm_num [Wu04MainPayment.pS])
  have hq := product_bounds Wu04MainPayment.qS (by norm_num [Wu04MainPayment.qS])
  have hp' : Wu04MainPayment.pS.prod=row1.S/row1.s := by norm_num [Wu04MainPayment.pS,row1]
  have hq' : Wu04MainPayment.qS.prod=(row1.S-1)/(row1.s-1) := by norm_num [Wu04MainPayment.qS,row1]
  rw [hp'] at hp
  rw [hq'] at hq
  apply pay_j (by norm_num [row1]) (by norm_num [row1])
    (by norm_num [Wu04MainClassical.a,row1])
    (by norm_num [yl,Wu04MainClassical.a,row1]) (by norm_num [yu,Wu04MainClassical.a,row1])
    (by norm_num [yl,Wu04MainClassical.a,row1]) (by norm_num [yu,Wu04MainClassical.a,row1])
    (by norm_num [c1,cubic,Wu04MainClassical.a,row1]) (by norm_num [c1,cubic,Wu04MainClassical.a,row1]) hp.2.1 hq.2.1 hq.1

theorem jK_payment : jKPaid≤lowerJ row1.kappa3 row1.kappa1 := by
  have hp := product_bounds Wu04MainPayment.pK (by norm_num [Wu04MainPayment.pK])
  have hq := product_bounds Wu04MainPayment.qK (by norm_num [Wu04MainPayment.qK])
  have hp' : Wu04MainPayment.pK.prod=row1.kappa1/row1.kappa3 := by norm_num [Wu04MainPayment.pK,row1]
  have hq' : Wu04MainPayment.qK.prod=(row1.kappa1-1)/(row1.kappa3-1) := by norm_num [Wu04MainPayment.qK,row1]
  rw [hp'] at hp
  rw [hq'] at hq
  apply pay_j (by norm_num [row1]) (by norm_num [row1])
    (by norm_num [Wu04MainClassical.a,row1])
    (by norm_num [yl,Wu04MainClassical.a,row1]) (by norm_num [yu,Wu04MainClassical.a,row1])
    (by norm_num [yl,Wu04MainClassical.a,row1]) (by norm_num [yu,Wu04MainClassical.a,row1])
    (by norm_num [c1,cubic,Wu04MainClassical.a,row1]) (by norm_num [c1,cubic,Wu04MainClassical.a,row1]) hp.2.1 hq.2.1 hq.1

def paidL (A l u : ℝ) : ℝ :=
  Wu04FactorLPrimitive.rationalPart (A-1)-Wu04FactorLPrimitive.rationalPart 2+u/5-l/20+
    (976/405)*up ((A+1)/4)-(536/405)*low ((3*A-5)/(A+1))

theorem pay_l {A l u : ℝ} (hA : 3≤A) (hl : l≤log (A-2)) (hu : log ((A-1)/2)≤u) :
    Wu04FactorLPrimitive.upperL A≤paidL A l u := by
  rw [Wu04FactorLPrimitive.collected hA]
  have h1 := (bounds (show 0<(A+1)/4 by linarith)).2
  have h2 := (bounds (show 0<(3*A-5)/(A+1) from div_pos (by linarith) (by linarith))).1
  unfold paidL
  linarith only [h1,h2,hl,hu]

def lSPaid : ℝ := paidL row1.S (pay Wu04MainPayment.lS) (upperPay Wu04MainPayment.uS)
def lKPaid : ℝ := paidL row1.kappa1 (pay Wu04MainPayment.lK) (upperPay Wu04MainPayment.uK)

theorem lS_payment : Wu04FactorLPrimitive.upperL row1.S≤lSPaid := by
  have hl := product_bounds Wu04MainPayment.lS (by norm_num [Wu04MainPayment.lS])
  have hu := product_bounds Wu04MainPayment.uS (by norm_num [Wu04MainPayment.uS])
  have hl' : Wu04MainPayment.lS.prod=row1.S-2 := by norm_num [Wu04MainPayment.lS,row1]
  have hu' : Wu04MainPayment.uS.prod=(row1.S-1)/2 := by norm_num [Wu04MainPayment.uS,row1]
  rw [hl'] at hl
  rw [hu'] at hu
  exact pay_l (by norm_num [row1]) hl.2.1 hu.2.2

theorem lK_payment : Wu04FactorLPrimitive.upperL row1.kappa1≤lKPaid := by
  have hl := product_bounds Wu04MainPayment.lK (by norm_num [Wu04MainPayment.lK])
  have hu := product_bounds Wu04MainPayment.uK (by norm_num [Wu04MainPayment.uK])
  have hl' : Wu04MainPayment.lK.prod=row1.kappa1-2 := by norm_num [Wu04MainPayment.lK,row1]
  have hu' : Wu04MainPayment.uK.prod=(row1.kappa1-1)/2 := by norm_num [Wu04MainPayment.uK,row1]
  rw [hl'] at hl
  rw [hu'] at hu
  exact pay_l (by norm_num [row1]) hl.2.1 hu.2.2

def classicalPaid : ℝ := jSPaid+jKPaid-2*lSPaid-2*lKPaid+2*lowerLog (20/19)-V (10/9)

theorem certificate_payment : classicalPaid≤Wu04FactorConsumer.classicalCertificate := by
  have hj := jS_payment
  have hk := jK_payment
  have hl := lS_payment
  have hm := lK_payment
  unfold classicalPaid Wu04FactorConsumer.classicalCertificate
  linarith only [hj,hk,hl,hm]

theorem classical_rational : (239459:ℝ)/1000000≤classicalPaid := by
  norm_num [classicalPaid,jSPaid,jKPaid,lSPaid,lKPaid,paidJ,paidL,paid,signedLow,low,up,
    rest,ratio,yl,yu,c0,c1,cubic,h2,h3,Wu04MainClassical.a,pay,upperPay,
    Wu04MainPayment.pS,Wu04MainPayment.pK,Wu04MainPayment.qS,Wu04MainPayment.qK,
    Wu04MainPayment.lS,Wu04MainPayment.lK,Wu04MainPayment.uS,Wu04MainPayment.uK,
    Wu04FactorLPrimitive.rationalPart,lower,upper,leftFactor,rightFactor,lowerLog,upperLog,V,row1]

end
end Wu04WholePayment
