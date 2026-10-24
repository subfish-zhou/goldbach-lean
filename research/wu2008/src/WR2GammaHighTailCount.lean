import WR2GammaHighTailIntegralCount
import WR2GammaHighTailUnitJDensity

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- Both original tail counts reach their J and K integrals at the same actual phi. -/
theorem actual_tail_integral_paid {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      gamma row N δ 20 + gamma row N δ 21 ≤
      (TailUnit.integralJMain row N δ + ∑ k : Bool, integralKMain row N δ k)*
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
        ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT1,h1⟩ := actual_tail_integral_density hd hh hr (half_pos he)
  obtain ⟨T2,_,h2⟩ := TailUnit.actual_unit_J_density hd hh hr (half_pos he)
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN hn row
  have ha := h1 N (by omega) hn row
  have hb := h2 N (by omega) hn row
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true] at ha ⊢
  linarith only [ha,hb]

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.actual_tail_integral_paid
