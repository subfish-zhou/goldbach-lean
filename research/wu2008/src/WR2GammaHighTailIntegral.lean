import WR2GammaHighTailQuadrature

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- All original nonunit main terms reach the continuous K integrals.
The actual phi and convolution weights remain; scalar error and quadrature share epsilon. -/
theorem rough_mass_tail_integral_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Bool, (roughFamily j N δ k).mass ≤ integralKMain j N δ k +
        (ε/2)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Bool, (roughFamily j N δ k).mass) ≤
        (∑ k : Bool, integralKMain j N δ k) +
          ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  obtain ⟨T1,hT1,h1⟩ := rough_mass_tail_finite_paid hd hh (half_pos he)
  obtain ⟨T2,_,h2⟩ := closedKMain_integral_paid hd hh (by positivity : 0 < ε/4)
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN j
  have hs (k : Bool) : (roughFamily j N δ k).mass ≤ integralKMain j N δ k +
      (ε/2)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
    have ha := (h1 N (by omega) j).1 k
    have hb := h2 N (by omega) j k
    have hc := finiteBuchstabMain_le_sourceClosedKMass j (by omega : 4 ≤ N) hd hh k
    linarith only [ha,hb,hc]
  refine ⟨hs,?_⟩
  have hsum := sum_le_sum (s := (univ : Finset (Bool))) (fun k _ => hs k)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_ofNat, show (2:ℝ)*((ε/2)*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (windows j N)) =
      ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) by ring] using hsum

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.rough_mass_tail_integral_paid
