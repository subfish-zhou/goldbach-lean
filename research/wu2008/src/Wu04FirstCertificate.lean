import Wu04FirstMass

namespace Wu04FirstCertificate
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Real
open Wu04FirstCost Wu04FirstClassical
open SecondFunctionalGeometricMass.Elementary
noncomputable section

/-- The full ordered selected-square mass, before any logarithmic enclosure. -/
theorem moment_exact (l h : ℝ) : elementaryMomentOne 1 l h =
    (1/l+1/h)*log (h/l)-2/l+2/h := by
  norm_num [elementaryMomentOne,elementaryMomentZero,momentPolynomial]
  ring

def massCap (i : Fin 5) : ℝ :=
  (1/lo i+1/hi i)*Wu04FactorEnvelopes.upper (hi i/lo i)-2/lo i+2/hi i

def costCap (i : Fin 5) : ℝ := Wu04MainTail.cap*massCap i-Wu04FirstMass.gain i

theorem mass_paid (i : Fin 5) : elementaryMomentOne 1 (lo i) (hi i)≤massCap i := by
  have g := Wu04FirstCost.geometry i
  have hh := g.2.1.trans_le (g.2.2.1.trans g.2.2.2)
  have hl := Wu04FactorEnvelopes.log_le_upper ((one_le_div g.2.1).mpr (g.2.2.1.trans g.2.2.2))
  have hm := mul_le_mul_of_nonneg_left hl (add_nonneg (one_div_nonneg.mpr g.2.1.le) (one_div_nonneg.mpr hh.le))
  rw [moment_exact]
  unfold massCap
  linarith only [hm]

theorem cost_paid (i : Fin 5) : omega3XIntegralEnvelope (firstNode i) (firstS i)≤costCap i := by
  have he := Wu04FirstMass.envelope_paid i
  have hm := mul_le_mul_of_nonneg_left (mass_paid i)
    (show 0≤Wu04MainTail.cap by norm_num [Wu04MainTail.cap])
  unfold costCap
  linarith only [he,hm]

def base (i : Fin 4) : ℝ := classicalPaid i-costCap i.castSucc

theorem base_paid (i : Fin 4) : base i≤firstFunctionalGainPsiOne (firstNode i.castSucc) (firstS i.castSucc) := by
  rw [Wu04FirstCore.psi_identity]
  unfold base
  linarith only [classical_paid i,cost_paid i.castSucc]

/-- The complete original positive-delta source with both certified sides consumed. -/
theorem actual (i : Fin 4) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    base i-deltaLoss δ*costCap i.castSucc+
      firstFeedback (actualNine δ) (firstNode i.castSucc) (firstS i.castSucc)≤
      wuImprovementLimit true δ (firstNode i.castSucc) := by
  have g := first_geometry i.castSucc
  have ha := first_actual hd hh g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2
  have hl : 0≤deltaLoss δ := by
    unfold deltaLoss
    exact div_nonneg (mul_nonneg (by norm_num) hd.le) (by linarith only [hh])
  have hc := mul_le_mul_of_nonneg_left (cost_paid i.castSucc) hl
  linarith only [ha,hc,base_paid i]

end
end Wu04FirstCertificate
