import WR2GammaHighLowerTripleIntegral
import WR2GammaHighLowerTripleUnitNegligible

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- Pay unit mass, scalar error, shifted boundary and quadrature in one budget. -/
theorem rough_mass_integral_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 6, (roughFamily j N δ k).mass ≤ integralKMain j N δ k +
          (ε/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 6, (roughFamily j N δ k).mass) ≤
        (∑ k : Fin 6, integralKMain j N δ k) +
          ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT1,h1⟩ := rough_mass_six_finite_paid hd hh he3
  obtain ⟨T2,_,h2⟩ := unitMass_six_negligible hd hh he3
  obtain ⟨T3,_,h3⟩ := finiteMain_six_integral_paid hd hh he3
  refine ⟨max T1 (max T2 T3),by omega,?_⟩
  intro N hN j
  have ha := h1 N (by omega) j
  have hb := h2 N (by omega) j
  have hc := h3 N (by omega) j
  constructor
  · intro k
    have h := ha.1 k
    have g := hb.1 k
    have f := hc.1 k
    linarith only [h,g,f]
  · have h := ha.2
    have g := hb.2
    have f := hc.2
    simp only [sum_add_distrib] at h
    linarith only [h,g,f]

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.rough_mass_integral_paid
