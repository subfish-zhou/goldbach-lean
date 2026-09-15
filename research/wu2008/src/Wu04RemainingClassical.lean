import Wu04RemainingCost

namespace Wu04RemainingClassical
open Wu2008DoubleSieve Real Wu04RemainingCore
open Wu04FactorEnvelopes Wu04FactorJPrimitive Wu04WholeCollection
noncomputable section

/-- Existing one-factor envelopes at the original J endpoint ratios; no new cut. -/
def jCertificate (B A : ℝ) : ℝ :=
  Wu04WholePayment.paidJ B A (lower (A/B)) (lower ((A-1)/(B-1)))

theorem lower_nonneg {x : ℝ} (hx : 1≤x) : 0≤lower x := by
  have h1 := (factors hx).1
  have h2 := (factors hx).2.1
  unfold lower SharpLogRecurrence.lowerLog
  positivity

theorem jCertificate_paid {B A : ℝ} (hB : 1<B) (hBA : B≤A)
    (ha : 1≤Wu04MainClassical.a B A)
    (hl1 : 0<yl B A (3*Wu04MainClassical.a B A-1))
    (hu1 : 0<yu A A (3*Wu04MainClassical.a B A-1))
    (hl2 : 0<yl B (3*A) (Wu04MainClassical.a B A-3))
    (hu2 : 0<yu A (3*A) (Wu04MainClassical.a B A-3))
    (hc1 : 0≤c1 1 (-4*Wu04MainClassical.a B A) A (3*Wu04MainClassical.a B A-1))
    (hc2 : 0≤c1 (1/3) (-4*Wu04MainClassical.a B A/3) (3*A) (Wu04MainClassical.a B A-3)) :
    jCertificate B A≤lowerJ B A := by
  have hp : 1≤A/B := (le_div_iff₀ (by linarith : 0<B)).mpr (by linarith)
  have hq : 1≤(A-1)/(B-1) := (le_div_iff₀ (by linarith : 0<B-1)).mpr (by linarith)
  exact Wu04WholePayment.pay_j hB (hB.trans_le hBA) ha hl1 hu1 hl2 hu2 hc1 hc2
    (lower_le_log hp) (lower_le_log hq) (lower_nonneg hq)

/-- Signed endpoint bounds handle the original reversed L(k2) without dropping it. -/
def lCertificate (A : ℝ) : ℝ := Wu04WholePayment.paidL A (low (A-2)) (up ((A-1)/2))

theorem lCertificate_paid {A : ℝ} (hA : 2<A) :
    Wu04FactorLPrimitive.upperL A≤lCertificate A := by
  rw [Wu04WholeReverseL.collected_small hA]
  have h1 := (bounds (show 0<(A+1)/4 by linarith)).2
  have h2 := (bounds (show 0<(3*A-5)/(A+1) from div_pos (by linarith) (by linarith))).1
  have h3 := (bounds (show 0<A-2 by linarith)).1
  have h4 := (bounds (show 0<(A-1)/2 by linarith)).2
  unfold lCertificate Wu04WholePayment.paidL
  linarith only [h1,h2,h3,h4]

def certificate (p : SecondFunctionalParameters) : ℝ :=
  jCertificate p.s p.S+jCertificate p.kappa3 p.kappa1-
  2*lCertificate p.S-2*lCertificate p.kappa1-lCertificate p.kappa2

theorem remaining_j (i : Fin 3) :
    jCertificate (row i).s (row i).S≤lowerJ (row i).s (row i).S ∧
    jCertificate (row i).kappa3 (row i).kappa1≤lowerJ (row i).kappa3 (row i).kappa1 := by
  revert i
  simp only [row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  repeat' constructor
  all_goals apply jCertificate_paid
  all_goals norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,
    SecondFunctionalParameters.row4,Wu04MainClassical.a,yl,yu,c1,cubic]

theorem remaining_paid (i : Fin 3) : certificate (row i)≤Wu08OriginalPsiRecovery.classicalNumerator (row i) := by
  have hj := remaining_j i
  have g := (ActualNineFeedback.coupledRow_geometry i.succ).1
  have hS : 2<(row i).S := lt_of_lt_of_le (by norm_num) g.three_le_S
  have hK : 2<(row i).kappa1 := lt_of_lt_of_le (by norm_num) (ActualNineFeedback.coupledRow_geometry i.succ).2.1
  have h2 : 2<(row i).kappa2 := g.two_lt_s.trans_le (g.mother.s_le_kappa3.trans g.mother.kappa3_lt_kappa2.le)
  have lS := lCertificate_paid hS
  have lK := lCertificate_paid hK
  have l2 := lCertificate_paid h2
  have hc := remaining_classical i
  unfold certificate classicalCore at *
  linarith only [hj.1,hj.2,lS,lK,l2,hc]

end
end Wu04RemainingClassical
