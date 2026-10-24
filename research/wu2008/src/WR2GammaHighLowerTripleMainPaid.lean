import WR2GammaHighLowerTripleFinitePaid

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- Both analytic approximations retain their main terms and share one error budget. -/
theorem rough_mass_main_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 6, (roughFamily j N δ k).mass ≤
        unitPrimeMain j N δ k + finiteBuchstabMain j N δ k +
          (ε/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 6, (roughFamily j N δ k).mass) ≤
        (∑ k : Fin 6, (unitPrimeMain j N δ k + finiteBuchstabMain j N δ k)) +
          ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  obtain ⟨T1,hT1,h1⟩ := rough_mass_six_finite_paid hd hh (half_pos he)
  obtain ⟨T2,_,h2⟩ := unitMass_six_prime_paid hd hh (half_pos he)
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN j
  have ha := h1 N (by omega) j
  have hb := h2 N (by omega) j
  constructor
  · intro k
    have h := ha.1 k
    have g := hb.1 k
    linarith only [h,g]
  · have h := ha.2
    have g := hb.2
    simp only [sum_add_distrib] at h ⊢
    linarith only [h,g]

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.rough_mass_main_paid
