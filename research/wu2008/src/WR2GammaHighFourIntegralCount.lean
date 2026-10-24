import WR2GammaHighFourIntegralDensity

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- Actual Gamma16..19 with original unit terms and same-phi nonunit integrals. -/
theorem actual_four_integral_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      (∑ k : Fin 4, gamma j N δ (16+k.val)) ≤
        (∑ k : Fin 4, FourPrimeUnit.actualSource N δ (Wu04RemainingCore.row j) (windows j N) k) +
        (∑ k : Fin 4, integralKMain j N δ k)*
          ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := nonunit_four_integral_density hd hh hr he
  refine ⟨T,hT,?_⟩
  intro N hN hn j
  have hu := sum_le_sum (s := (univ : Finset (Fin 4)))
    (fun k _ => actual_source_upper j δ k (hT.trans hN) hn)
  rw [sum_add_distrib] at hu
  have hm := (h N hN hn j).2
  exact hu.trans (by simpa only [add_assoc] using add_le_add le_rfl hm)

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.actual_four_integral_density
