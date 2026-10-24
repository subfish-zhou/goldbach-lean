import WR2GammaHighFourFiniteError

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Real Finset
open scoped Classical

/-- The four words retain their finite main terms; only the scalar error is paid. -/
theorem rough_mass_four_finite_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 4, (roughFamily j N δ k).mass ≤ finiteBuchstabMain j N δ k +
        (ε/4) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 4, (roughFamily j N δ k).mass) ≤ (∑ k : Fin 4, finiteBuchstabMain j N δ k) +
        ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
  let C : ℝ := 5^4/highEta
  have hC : 0 < C := by norm_num [C, highEta]
  obtain ⟨T0,hT0,h0⟩ := rough_mass_finite_buchstab hδ hδhi (div_pos hε (mul_pos (by norm_num) hC) : 0 < ε/(4*C))
  obtain ⟨T1,_,h1⟩ := LowerTriple.high_slab_mass hδ hδhi
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN j
  have hN0 := (le_max_left T0 T1).trans hN
  have hN1 := (le_max_right T0 T1).trans hN
  have hs (k : Fin 4) : (roughFamily j N δ k).mass ≤ finiteBuchstabMain j N δ k +
      (ε/4) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
    have he := finiteErrorMass_le j k (hT0.trans hN0) hδ hδhi (h1 N hN1 j)
    apply (h0 N hN0 j k).trans
    apply add_le_add le_rfl
    calc
      _ ≤ (ε/(4*C)) * (C * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by field_simp
  refine ⟨hs,?_⟩
  have hh := sum_le_sum (s := (univ : Finset (Fin 4))) (fun k _ => hs k)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (4:ℝ)*((ε/4)*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (windows j N)) =
      ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) by ring] using hh

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.rough_mass_four_finite_paid
