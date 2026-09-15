import Wu04RemainingTail

namespace Wu04RemainingStrongClassical
open Wu2008DoubleSieve Real Wu04RemainingCore
open Wu04WholeCollection Wu04WholePayment Wu04FactorEnvelopes Wu04FactorJPrimitive
noncomputable section

/-- Transport the existing fixed chain to the original row endpoint; no new cut. -/
def chainLow (xs : List ℝ) (x : ℝ) : ℝ := pay xs + low (x/xs.prod)
def chainUp (xs : List ℝ) (x : ℝ) : ℝ := upperPay xs + up (x/xs.prod)

theorem chain_bounds (xs : List ℝ) (hx : ∀ t∈xs, (1:ℝ)≤t) {x : ℝ} (hp : 0<x) :
    chainLow xs x≤log x ∧ log x≤chainUp xs x := by
  have hprod : 0<xs.prod := List.prod_pos (fun t ht => lt_of_lt_of_le (by norm_num) (hx t ht))
  have hb := product_bounds xs hx
  have hc := bounds (div_pos hp hprod)
  rw [log_div hp.ne' hprod.ne'] at hc
  unfold chainLow chainUp
  constructor <;> linarith only [hb.2.1,hb.2.2,hc.1,hc.2]

def jS (p : SecondFunctionalParameters) : ℝ :=
  paidJ p.s p.S (chainLow Wu04MainPayment.pS (p.S/p.s))
    (chainLow Wu04MainPayment.qS ((p.S-1)/(p.s-1)))
def jK (p : SecondFunctionalParameters) : ℝ :=
  paidJ p.kappa3 p.kappa1 (chainLow Wu04MainPayment.pK (p.kappa1/p.kappa3))
    (chainLow Wu04MainPayment.qK ((p.kappa1-1)/(p.kappa3-1)))
def lS (p : SecondFunctionalParameters) : ℝ :=
  paidL p.S (chainLow Wu04MainPayment.lS (p.S-2))
    (chainUp Wu04MainPayment.uS ((p.S-1)/2))
def lK (p : SecondFunctionalParameters) : ℝ :=
  paidL p.kappa1 (chainLow Wu04MainPayment.lK (p.kappa1-2))
    (chainUp Wu04MainPayment.uK ((p.kappa1-1)/2))
def certificate (p : SecondFunctionalParameters) : ℝ :=
  jS p+jK p-2*lS p-2*lK p-Wu04RemainingClassical.lCertificate p.kappa2

theorem remaining_j (i : Fin 3) : jS (row i)≤lowerJ (row i).s (row i).S ∧
    jK (row i)≤lowerJ (row i).kappa3 (row i).kappa1 := by
  have hgen {B A : ℝ} (xs ys : List ℝ) (hx : ∀ t∈xs,(1:ℝ)≤t)
      (hy : ∀ t∈ys,(1:ℝ)≤t) (hB : 1<B) (hA : 1<A)
      (ha : 1≤Wu04MainClassical.a B A)
      (hl1 : 0<yl B A (3*Wu04MainClassical.a B A-1))
      (hu1 : 0<yu A A (3*Wu04MainClassical.a B A-1))
      (hl2 : 0<yl B (3*A) (Wu04MainClassical.a B A-3))
      (hu2 : 0<yu A (3*A) (Wu04MainClassical.a B A-3))
      (hc1 : 0≤c1 1 (-4*Wu04MainClassical.a B A) A (3*Wu04MainClassical.a B A-1))
      (hc2 : 0≤c1 (1/3) (-4*Wu04MainClassical.a B A/3) (3*A) (Wu04MainClassical.a B A-3))
      (hq : 0≤chainLow ys ((A-1)/(B-1))) :
      paidJ B A (chainLow xs (A/B)) (chainLow ys ((A-1)/(B-1)))≤lowerJ B A :=
    pay_j hB hA ha hl1 hu1 hl2 hu2 hc1 hc2
      (chain_bounds xs hx (div_pos (by linarith) (by linarith))).1
      (chain_bounds ys hy (div_pos (by linarith) (by linarith))).1 hq
  revert i
  simp only [row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  repeat' constructor
  all_goals simp only [jS,jK]
  all_goals apply hgen
  all_goals norm_num [Wu04MainPayment.pS,Wu04MainPayment.qS,Wu04MainPayment.pK,Wu04MainPayment.qK,
    SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4,
    Wu04MainClassical.a,yl,yu,c1,cubic,chainLow,pay,low,lower,upper,leftFactor,rightFactor,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,JointLogTotalComparison.V]

theorem remaining_l (i : Fin 3) : Wu04FactorLPrimitive.upperL (row i).S≤lS (row i) ∧
    Wu04FactorLPrimitive.upperL (row i).kappa1≤lK (row i) := by
  have g := ActualNineFeedback.coupledRow_geometry i.succ
  have hS : 3≤(row i).S := g.1.three_le_S
  have hK : 3≤(row i).kappa1 := g.2.1
  constructor
  · exact pay_l hS
      (chain_bounds Wu04MainPayment.lS (by norm_num [Wu04MainPayment.lS]) (by linarith)).1
      (chain_bounds Wu04MainPayment.uS (by norm_num [Wu04MainPayment.uS]) (by linarith)).2
  · exact pay_l hK
      (chain_bounds Wu04MainPayment.lK (by norm_num [Wu04MainPayment.lK]) (by linarith)).1
      (chain_bounds Wu04MainPayment.uK (by norm_num [Wu04MainPayment.uK]) (by linarith)).2

theorem complete_paid (i : Fin 3) : certificate (row i)≤Wu08OriginalPsiRecovery.classicalNumerator (row i) := by
  have hj := remaining_j i
  have hl := remaining_l i
  have g := (ActualNineFeedback.coupledRow_geometry i.succ).1
  have h2 : 2<(row i).kappa2 := g.two_lt_s.trans_le (g.mother.s_le_kappa3.trans g.mother.kappa3_lt_kappa2.le)
  have hr := Wu04RemainingClassical.lCertificate_paid h2
  have hc := remaining_classical i
  unfold certificate classicalCore at *
  linarith only [hj.1,hj.2,hl.1,hl.2,hr,hc]
end
end Wu04RemainingStrongClassical
