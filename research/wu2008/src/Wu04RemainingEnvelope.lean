import Wu04RemainingClassical

namespace Wu04RemainingEnvelope
open Wu2008DoubleSieve Real Wu04RemainingCore Wu04RemainingCost Wu04FactorEnvelopes Wu04FullPsiMass
noncomputable section

def lx (p : SecondFunctionalParameters) : ℝ := lower ((1/p.kappa1)/(1/p.S))
def ux (p : SecondFunctionalParameters) : ℝ := upper ((1/p.kappa1)/(1/p.S))
def ly (p : SecondFunctionalParameters) : ℝ := lower ((1/p.kappa2)/(1/p.kappa1))
def uy (p : SecondFunctionalParameters) : ℝ := upper ((1/p.kappa2)/(1/p.kappa1))
def lz (p : SecondFunctionalParameters) : ℝ := lower ((1/p.kappa3)/(1/p.kappa2))
def uz (p : SecondFunctionalParameters) : ℝ := upper ((1/p.kappa3)/(1/p.kappa2))
def lw (p : SecondFunctionalParameters) : ℝ := lower ((1/p.s)/(1/p.kappa3))
def uw (p : SecondFunctionalParameters) : ℝ := upper ((1/p.s)/(1/p.kappa3))

theorem log_bounds (i : Fin 3) :
    lx (row i)≤x (row i) ∧ x (row i)≤ux (row i) ∧
    ly (row i)≤y (row i) ∧ y (row i)≤uy (row i) ∧
    lz (row i)≤z (row i) ∧ z (row i)≤uz (row i) ∧
    lw (row i)≤w (row i) ∧ w (row i)≤uw (row i) ∧
    0≤lx (row i) ∧ 0≤ly (row i) ∧ 0≤lz (row i) ∧ 0≤lw (row i) := by
  obtain ⟨ha,hab,hbc,hcd,hde,_⟩ := LowerTripleContinuous.mother_compact_parameters (row i)
    (SecondFunctionalFourSevenths.original_mother i.succ) (SecondFunctionalFourSevenths.original_s_ge_two i.succ)
  have ha0 : 0<1/(row i).S := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hd0 := hc0.trans_le hcd
  have hx := (one_le_div ha0).mpr hab
  have hy := (one_le_div hb0).mpr hbc
  have hz := (one_le_div hc0).mpr hcd
  have hw := (one_le_div hd0).mpr hde
  exact ⟨lower_le_log hx,log_le_upper hx,lower_le_log hy,log_le_upper hy,
    lower_le_log hz,log_le_upper hz,lower_le_log hw,log_le_upper hw,
    Wu04RemainingClassical.lower_nonneg hx,Wu04RemainingClassical.lower_nonneg hy,
    Wu04RemainingClassical.lower_nonneg hz,Wu04RemainingClassical.lower_nonneg hw⟩

def tripleCap (p : SecondFunctionalParameters) : ℝ :=
  (p.kappa1-p.kappa2+2*p.kappa3)*uy p+(2*p.kappa1-p.kappa2+p.kappa3)*uz p+
  (p.S-p.kappa2)*uw p-p.kappa3*ly p*lw p+p.kappa1*ux p*uz p+
  (p.s-p.kappa2)*lx p-2*(p.kappa1-p.kappa3)

def fourCap (p : SecondFunctionalParameters) : ℝ :=
  (p.kappa2+2*p.kappa3)*uz p+(p.kappa2-p.kappa3)*uw p-p.kappa3*lz p*lw p+
  (p.s/2)*(uz p)^2-3*(p.kappa2-p.kappa3)+(p.kappa3+p.s)*uy p*uw p-
  2*(p.kappa3-p.s)*ly p

def highCap (p : SecondFunctionalParameters) : ℝ := uz p*(uw p)^3/(24*(1/p.kappa3))
def costCap (p : SecondFunctionalParameters) : ℝ := Wu04MainTail.cap*tripleCap p+fourCap p+highCap p

theorem polynomials_paid (i : Fin 3) : triplePolynomial (row i)≤tripleCap (row i) ∧
    fourPolynomial (row i)≤fourCap (row i) := by
  obtain ⟨hx,hX,hy,hY,hz,hZ,hw,hW,hx0,hy0,hz0,hw0⟩ := log_bounds i
  have yw := mul_le_mul hy hw hw0 (hy0.trans hy)
  have xz := mul_le_mul hX hZ (hz0.trans hz) (hx0.trans (hx.trans hX))
  have zw := mul_le_mul hz hw hw0 (hz0.trans hz)
  have YW := mul_le_mul hY hW (hw0.trans hw) (hy0.trans (hy.trans hY))
  have zz := pow_le_pow_left₀ (hz0.trans hz) hZ 2
  have g : MotherPair.AnalyticParameters (row i) := (ActualNineFeedback.coupledRow_geometry i.succ).1
  have h3 : 0≤(row i).kappa3 := (by linarith [g.two_lt_s,g.mother.s_le_kappa3])
  have h1 : 0≤(row i).kappa1 := h3.trans (g.mother.kappa3_lt_kappa2.le.trans g.mother.kappa2_lt_kappa1.le)
  have hs : 0≤(row i).s := by linarith [g.two_lt_s]
  have k32 := g.mother.kappa3_lt_kappa2.le
  have k21 := g.mother.kappa2_lt_kappa1.le
  have s3 := g.mother.s_le_kappa3
  have kS := g.mother.kappa1_le_S
  have a := mul_le_mul_of_nonneg_left hY (show 0≤(row i).kappa1-(row i).kappa2+2*(row i).kappa3 by linarith)
  have b := mul_le_mul_of_nonneg_left hZ (show 0≤2*(row i).kappa1-(row i).kappa2+(row i).kappa3 by linarith)
  have c := mul_le_mul_of_nonneg_left hW (show 0≤(row i).S-(row i).kappa2 by linarith)
  have d := mul_le_mul_of_nonneg_left yw h3
  have e := mul_le_mul_of_nonneg_left xz h1
  have f := mul_le_mul_of_nonpos_left hx (show (row i).s-(row i).kappa2≤0 by linarith)
  have a' := mul_le_mul_of_nonneg_left hZ (show 0≤(row i).kappa2+2*(row i).kappa3 by linarith)
  have b' := mul_le_mul_of_nonneg_left hW (show 0≤(row i).kappa2-(row i).kappa3 by linarith)
  have c' := mul_le_mul_of_nonneg_left zw h3
  have d' := mul_le_mul_of_nonneg_left zz (div_nonneg hs (by norm_num : (0:ℝ)≤2))
  have e' := mul_le_mul_of_nonneg_left YW (add_nonneg h3 hs)
  have f' := mul_le_mul_of_nonneg_left hy (show 0≤2*((row i).kappa3-(row i).s) by linarith)
  constructor
  · unfold triplePolynomial tripleCap
    nlinarith only [a,b,c,d,e,f]
  · unfold fourPolynomial fourCap
    nlinarith only [a',b',c',d',e',f']

theorem high_paid (i : Fin 3) : Wu04HighCoupledSupport.U20 (row i)≤highCap (row i) := by
  obtain ⟨_,_,_,_,hz,hZ,hw,hW,_,_,hz0,hw0⟩ := log_bounds i
  have hm := mul_le_mul hZ (pow_le_pow_left₀ (hw0.trans hw) hW 3)
    (pow_nonneg (hw0.trans hw) 3) (hz0.trans (hz.trans hZ))
  have hden : 0≤24*(1/(row i).kappa3) := by
    have hg : MotherPair.AnalyticParameters (row i) := (ActualNineFeedback.coupledRow_geometry i.succ).1
    have h3 : 0<(row i).kappa3 := by linarith [hg.two_lt_s,hg.mother.s_le_kappa3]
    positivity
  exact div_le_div_of_nonneg_right hm hden

theorem complete_paid (i : Fin 3) : ActualNineFeedback.coupledCostMass (row i)≤costCap (row i) := by
  have hc := Wu04RemainingCost.complete_paid i
  have ht := mul_le_mul_of_nonneg_left (polynomials_paid i).1
    (show 0≤Wu04MainTail.cap by norm_num [Wu04MainTail.cap])
  have hf := (polynomials_paid i).2
  have hh := high_paid i
  unfold costCore costCap at *
  linarith only [hc,ht,hf,hh]

end
end Wu04RemainingEnvelope
