import WR2GammaHighLowerTripleFiniteError

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite HighBoxRecovery Real Finset
open scoped Classical

/-- The six bands retain both main terms; only the nonunit scalar error is paid. -/
theorem rough_mass_six_finite_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 6, (roughFamily j N δ k).mass ≤ (unitMass j N δ k + finiteBuchstabMain j N δ k) +
        (ε/6) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 6, (roughFamily j N δ k).mass) ≤ (∑ k : Fin 6, (unitMass j N δ k + finiteBuchstabMain j N δ k)) +
        ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
  let C : ℝ := 5^3/highEta
  have hC : 0 < C := by norm_num [C, highEta]
  obtain ⟨T0,hT0,h0⟩ := rough_mass_finite_buchstab hδ hδhi (div_pos hε (mul_pos (by norm_num) hC) : 0 < ε/(6*C))
  obtain ⟨T1,_,h1⟩ := high_slab_mass hδ hδhi
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN j
  have hN0 := (le_max_left T0 T1).trans hN
  have hN1 := (le_max_right T0 T1).trans hN
  have hs (k : Fin 6) : (roughFamily j N δ k).mass ≤ (unitMass j N δ k + finiteBuchstabMain j N δ k) +
      (ε/6) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
    have he := finiteErrorMass_le j k (hT0.trans hN0) hδ hδhi (h1 N hN1 j)
    apply (h0 N hN0 j k).trans
    apply add_le_add le_rfl
    calc
      _ ≤ (ε/(6*C)) * (C * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by field_simp
  refine ⟨hs,?_⟩
  have hh := sum_le_sum (s := (univ : Finset (Fin 6))) (fun k _ => hs k)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (6:ℝ)*((ε/6)*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (windows j N)) =
      ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) by ring] using hh

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.rough_mass_six_finite_paid
