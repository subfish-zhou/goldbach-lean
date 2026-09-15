import Wu04FirstCore

namespace Wu04FirstClassical
open Wu2008DoubleSieve ActualNineFeedback Real
open Wu04RemainingStrongClassical Wu04WholePayment Wu04WholeCollection Wu04FactorJPrimitive
noncomputable section

/-- Only the already fixed endpoint chains, with a signed residual at the actual Psi1 endpoint. -/
def jPaid (i : Fin 4) : ℝ :=
  paidJ (firstNode i.castSucc) (firstS i.castSucc)
    (chainLow Wu04MainPayment.pK (firstS i.castSucc/firstNode i.castSucc))
    (chainLow Wu04MainPayment.qK ((firstS i.castSucc-1)/(firstNode i.castSucc-1)))
def lPaid (i : Fin 4) : ℝ :=
  paidL (firstS i.castSucc)
    (chainLow Wu04MainPayment.lK (firstS i.castSucc-2))
    (chainUp Wu04MainPayment.uK ((firstS i.castSucc-1)/2))
def classicalPaid (i : Fin 4) : ℝ := jPaid i/2-lPaid i

theorem geometry (i : Fin 4) :
    2<firstNode i.castSucc ∧ firstNode i.castSucc≤firstS i.castSucc ∧
    1<Wu04MainClassical.a (firstNode i.castSucc) (firstS i.castSucc) ∧
    Wu04MainClassical.a (firstNode i.castSucc) (firstS i.castSucc)≠3 := by
  revert i
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,
    firstS,Fin.castSucc_zero,Fin.castSucc_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [firstNode,Wu04MainClassical.a]

theorem j_paid (i : Fin 4) : jPaid i≤fourthRowClassicalJ (firstNode i.castSucc) (firstS i.castSucc) := by
  have g := geometry i
  apply le_trans _ (actual_lower g.1 g.2.1 g.2.2.1 g.2.2.2)
  have hgen {B A : ℝ} (hB : 1<B) (hA : 1<A) (ha : 1≤Wu04MainClassical.a B A)
      (hl1 : 0<yl B A (3*Wu04MainClassical.a B A-1))
      (hu1 : 0<yu A A (3*Wu04MainClassical.a B A-1))
      (hl2 : 0<yl B (3*A) (Wu04MainClassical.a B A-3))
      (hu2 : 0<yu A (3*A) (Wu04MainClassical.a B A-3))
      (hc1 : 0≤c1 1 (-4*Wu04MainClassical.a B A) A (3*Wu04MainClassical.a B A-1))
      (hc2 : 0≤c1 (1/3) (-4*Wu04MainClassical.a B A/3) (3*A) (Wu04MainClassical.a B A-3))
      (hq : 0≤chainLow Wu04MainPayment.qK ((A-1)/(B-1))) :
      paidJ B A (chainLow Wu04MainPayment.pK (A/B))
        (chainLow Wu04MainPayment.qK ((A-1)/(B-1)))≤lowerJ B A :=
    pay_j hB hA ha hl1 hu1 hl2 hu2 hc1 hc2
      (chain_bounds _ (by norm_num [Wu04MainPayment.pK]) (div_pos (by linarith) (by linarith))).1
      (chain_bounds _ (by norm_num [Wu04MainPayment.qK]) (div_pos (by linarith) (by linarith))).1 hq
  clear g
  revert i
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  repeat' constructor
  all_goals unfold jPaid
  all_goals apply hgen
  all_goals simp only [firstS,Fin.castSucc_zero,Fin.castSucc_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals norm_num [firstNode,Wu04MainClassical.a,
    yl,yu,c1,cubic,chainLow,Wu04MainPayment.qK,Wu04WholeCollection.pay,
    low,Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,JointLogTotalComparison.V]

theorem l_paid (i : Fin 4) : fourthRowClassicalL (firstS i.castSucc)≤lPaid i := by
  have g := first_geometry i.castSucc
  apply (Wu04FactorLPrimitive.actual_upper g.2.2.1).trans
  exact pay_l g.2.2.1
    (chain_bounds _ (by norm_num [Wu04MainPayment.lK]) (by linarith only [g.2.2.1])).1
    (chain_bounds _ (by norm_num [Wu04MainPayment.uK]) (by linarith only [g.2.2.1])).2

theorem classical_paid (i : Fin 4) : classicalPaid i≤
    fourthRowClassicalJ (firstNode i.castSucc) (firstS i.castSucc)/2-
      fourthRowClassicalL (firstS i.castSucc) := by
  unfold classicalPaid
  linarith only [j_paid i,l_paid i]
end
end Wu04FirstClassical
