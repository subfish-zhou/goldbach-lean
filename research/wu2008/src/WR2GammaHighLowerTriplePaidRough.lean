import WR2GammaHighLowerTripleExceptionPayment

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve Real

/-- Both purification exceptions are paid; the exact rough main is retained. -/
theorem paid_rough_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ k : Fin 6,
      gamma j N δ (10+k.val) ≤ (roughFamily j N δ k).mass*
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT1,h1⟩ := actual_rough_density hd hh hr he3
  obtain ⟨T2,_,h2⟩ := square_error_paid he3
  obtain ⟨T3,_,h3⟩ := bad_error_paid he3
  refine ⟨max T1 (max T2 T3),by omega,fun N hN hEven j k => ?_⟩
  have ha := h1 N (by omega) hEven j k
  have hb := h2 N (by omega)
  have hc := h3 N (by omega)
  linarith only [ha,hb,hc]

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.paid_rough_density
