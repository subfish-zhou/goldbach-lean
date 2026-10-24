import WR2GammaHighFourUnitPaid

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- All original Gamma16..19 terms, with unit sources and every error paid. -/
theorem actual_four_integral_paid {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      (∑ k : Fin 4, gamma j N δ (16+k.val)) ≤
        (∑ k : Fin 4, integralKMain j N δ k)*
          ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT1,h1⟩ := actual_four_integral_density hd hh hr (half_pos he)
  obtain ⟨T2,_,h2⟩ := FourUnit.unit_four_paid hd hh (half_pos he)
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN hn j
  have ha := h1 N (by omega) hn j
  have hb := h2 N (by omega) j
  linarith only [ha,hb]

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.actual_four_integral_paid
