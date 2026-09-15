import Wu04CurvePaid

namespace Wu04RemainingCore
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
open SecondFunctionalParameters
noncomputable section

/-- Only the remaining original rows, in their original order. -/
def row (i : Fin 3) : SecondFunctionalParameters := coupledRow i.succ

/-- Wu04 author TeX Table 1, lines 2803, 2819, 2835; targets, not premises. -/
def publication (i : Fin 3) : ℝ :=
  if i = 0 then 15247971/1000000000 else
  if i = 1 then 13898757/1000000000 else 11776059/1000000000

/-- The once-split J primitive and the SAME L primitive, including reversed L(k2). -/
def classicalCore (p : SecondFunctionalParameters) : ℝ :=
  Wu04FactorJPrimitive.lowerJ p.s p.S +
  Wu04FactorJPrimitive.lowerJ p.kappa3 p.kappa1 -
  2*Wu04FactorLPrimitive.upperL p.S -
  2*Wu04FactorLPrimitive.upperL p.kappa1 - Wu04FactorLPrimitive.upperL p.kappa2

theorem classical_core_paid {p : SecondFunctionalParameters}
    (hs : 2<p.s) (hsS : p.s≤p.S)
    (ha : 1<Wu04MainClassical.a p.s p.S) (ha3 : Wu04MainClassical.a p.s p.S≠3)
    (hk : 2<p.kappa3) (hk1 : p.kappa3≤p.kappa1)
    (hb : 1<Wu04MainClassical.a p.kappa3 p.kappa1)
    (hb3 : Wu04MainClassical.a p.kappa3 p.kappa1≠3)
    (hS : 3≤p.S) (h1 : 3≤p.kappa1) (h2 : 2<p.kappa2) (h23 : p.kappa2≤3) :
    classicalCore p ≤ classicalNumerator p := by
  have hj := Wu04FactorJPrimitive.actual_lower hs hsS ha ha3
  have hjk := Wu04FactorJPrimitive.actual_lower hk hk1 hb hb3
  have hl := Wu04FactorLPrimitive.actual_upper hS
  have hlk := Wu04FactorLPrimitive.actual_upper h1
  have hlr := Wu04WholeReverseL.actual_upper_small h2 h23
  unfold classicalCore classicalNumerator
  linarith only [hj,hjk,hl,hlk,hlr]

theorem remaining_classical (i : Fin 3) : classicalCore (row i)≤classicalNumerator (row i) := by
  have hall : ∀ i : Fin 3, classicalCore (row i)≤classicalNumerator (row i) := by
    simp only [row, coupledRow, SecondFunctionalPositive.parameters,
      Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    repeat' constructor
    all_goals apply classical_core_paid
    all_goals norm_num [row,coupledRow,SecondFunctionalPositive.parameters,
      row1,row2,row3,row4,Wu04MainClassical.a]
  exact hall i

/-- The literal original signed numerator and fixed-positive-delta cost. -/
theorem actual_of_paid {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {B C δ : ℝ} (hB : B≤classicalNumerator p) (hC : coupledCostMass p≤C)
    (hd : 0<δ) (hh : δ≤1/10) :
    B/5-2*C/(5*(1-2*δ))+coupledFeedback p (actualNine δ)≤wuImprovementLimit true δ p.s := by
  have h := original_logs_actual_lower hp hd hh
  have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ)≤2))
    (show 0≤5*(1-2*δ) by linarith)
  linarith only [h,hc,hB]

end
end Wu04RemainingCore
