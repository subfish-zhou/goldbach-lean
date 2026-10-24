import WR2GammaHighTailCount
import WR2GammaHighFourCount
import WR2GammaHighLowerTripleIntegralDensity

noncomputable section
namespace WuPaper.R2GammaHigh.Coupled
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- The fourteen integral masses retain the same original supported divisor and phi. -/
def integralMass (row : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  (∑ k : Fin 6, LowerTriple.integralKMain row N δ k) +
    (∑ k : Fin 4, Four.integralKMain row N δ k) +
    (TailUnit.integralJMain row N δ + ∑ k : Bool, Tail.integralKMain row N δ k)

theorem actual_twelve_integral_paid {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      (∑ k : Fin 6, gamma row N δ (10+k.val)) +
        (∑ k : Fin 4, gamma row N δ (16+k.val)) +
        (gamma row N δ 20 + gamma row N δ 21) ≤
      integralMass row N δ *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
        ε*truncatedSixthMassScale N := by
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT1,h1⟩ := LowerTriple.actual_six_integral_density hd hh hr he3
  obtain ⟨T2,_,h2⟩ := Four.actual_four_integral_paid hd hh hr he3
  obtain ⟨T3,_,h3⟩ := Tail.actual_tail_integral_paid hd hh hr he3
  refine ⟨max T1 (max T2 T3),by omega,?_⟩
  intro N hN hn row
  have ha := (h1 N (by omega) hn row).2
  have hb := h2 N (by omega) hn row
  have hc := h3 N (by omega) hn row
  unfold integralMass
  linarith only [ha,hb,hc]

end WuPaper.R2GammaHigh.Coupled
#print axioms WuPaper.R2GammaHigh.Coupled.actual_twelve_integral_paid
