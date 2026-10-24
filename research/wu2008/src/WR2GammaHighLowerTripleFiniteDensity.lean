import WR2GammaHighLowerTripleNormalization

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- Actual Gamma10..15, retaining the unit prime main and finite Buchstab main.
The six original bands share epsilon times the original counting scale. -/
theorem actual_six_finite_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      let D := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      (∀ k : Fin 6, gamma j N δ (10+k.val) ≤
        (unitPrimeMain j N δ k + finiteBuchstabMain j N δ k)*D +
          (ε/6)*truncatedSixthMassScale N) ∧
      (∑ k : Fin 6, gamma j N δ (10+k.val)) ≤
        (∑ k : Fin 6, (unitPrimeMain j N δ k + finiteBuchstabMain j N δ k))*D +
          ε*truncatedSixthMassScale N := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith) (by positivity))
    (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT0,h0⟩ := paid_rough_density hd hh hr (by positivity : 0 < ε/12)
  obtain ⟨T1,_,h1⟩ := rough_mass_main_paid hd hh (div_pos he (mul_pos (by norm_num) hA) : 0 < ε/(480*A))
  obtain ⟨T2,_,h2⟩ := reciprocal_mass_scale hd hh
  refine ⟨max T0 (max T1 T2),by omega,?_⟩
  intro N hN hn j
  have hN4 : 4 ≤ N := by omega
  have hC : 0 ≤ wuSingularSeries N/log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hm := (h1 N (by omega) j).1
  have hc := h2 N (by omega) hn j
  have hs (k : Fin 6) : gamma j N δ (10+k.val) ≤
      (unitPrimeMain j N δ k + finiteBuchstabMain j N δ k)*(A*wuSingularSeries N/log N) +
        (ε/6)*truncatedSixthMassScale N := by
    have hg := h0 N (by omega) hn j k
    have hb := mul_le_mul_of_nonneg_right (hm k) (mul_nonneg hA.le hC)
    have hp := mul_le_mul_of_nonneg_left hc (show 0 ≤ ε/2880 by positivity)
    have cancel : ((ε/(480*A)/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N))*
        (A*(wuSingularSeries N/log N)) =
        (ε/2880)*(wuSingularSeries N/log N*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N)) := by
      field_simp
      ring
    rw [add_mul,cancel] at hb
    change _ ≤ (roughFamily j N δ k).mass*(A*wuSingularSeries N/log N)+_ at hg
    rw [mul_div_assoc] at hg ⊢
    linarith only [hg,hb,hp]
  refine ⟨hs,?_⟩
  have hsum := sum_le_sum (s := (univ : Finset (Fin 6))) (fun k _ => hs k)
  simpa only [sum_add_distrib, ← sum_mul, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (6:ℝ)*(ε/6) = ε by ring] using hsum

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.actual_six_finite_density
