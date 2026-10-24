import WR2GammaHighLowerTripleBoundaryPaid
import WR2GammaHighLowerTripleQuadrature

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve Real Finset
open scoped Classical

theorem unshifted_le_closedK {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    unshiftedFiniteBuchstabMain j N δ k ≤ closedKMain j N δ k :=
  filtered_finiteBuchstabMain_le_closedPrimeKj j hN hd hh k

/-- All original nonunit main terms reach the continuous K integrals.
The actual phi and convolution weights remain; boundary and quadrature share epsilon. -/
theorem finiteMain_six_integral_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 6, finiteBuchstabMain j N δ k ≤ integralKMain j N δ k +
        (ε/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 6, finiteBuchstabMain j N δ k) ≤
        (∑ k : Fin 6, integralKMain j N δ k) +
          ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  obtain ⟨T1,hT1,h1⟩ := finiteMain_six_boundary_paid hd hh (half_pos he)
  obtain ⟨T2,_,h2⟩ := closedKMain_integral_paid hd hh (by positivity : 0 < ε/12)
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN j
  have hs (k : Fin 6) : finiteBuchstabMain j N δ k ≤ integralKMain j N δ k +
      (ε/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
    have ha := (h1 N (by omega) j).1 k
    have hb := h2 N (by omega) j k
    have hc := unshifted_le_closedK j k (by omega : 4 ≤ N) hd hh
    linarith only [ha,hb,hc]
  refine ⟨hs,?_⟩
  have hsum := sum_le_sum (s := (univ : Finset (Fin 6))) (fun k _ => hs k)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (6:ℝ)*((ε/6)*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (windows j N)) =
      ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) by ring] using hsum

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.finiteMain_six_integral_paid
