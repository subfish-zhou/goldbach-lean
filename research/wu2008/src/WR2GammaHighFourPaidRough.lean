import WR2GammaHighFourExceptionPayment

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Real Filter
open scoped Classical

/-- Both purification exceptions are paid; the actual rough raw mass is retained. -/
theorem paid_rough_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ k : Fin 4,
      (sourceFamily j N δ k).primeMass ≤ (roughFamily j N δ k).mass*
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT1,h1⟩ := restricted_density hd hh hr he3
  obtain ⟨T2,_,h2⟩ := square_error_paid he3
  obtain ⟨T3,_,h3⟩ := bad_error_paid he3
  obtain ⟨T4,h4⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : 0 < highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2:ℝ)))
  refine ⟨max T1 (max T2 (max T3 T4)),by omega,?_⟩
  intro N hN hn j k
  have hp := prime_mass_split j k (by omega : 2 ≤ N) hd hh
  have ha := h1 N (by omega) hn j k profileRough
  have hy := h4 N (by omega)
  dsimp only [Function.comp_apply] at hy
  have hb := (square_mass_bound j k (by omega : 2 ≤ N) hd hh hy).trans (h2 N (by omega))
  have hc := (bad_prime_bound j k (by omega : 2 ≤ N) hd hh).trans (h3 N (by omega))
  dsimp only [roughFamily] at hp ha ⊢
  linarith only [hp,ha,hb,hc]

/-- Original Gamma16..19 retain their unit terms and the same four nonunit words. -/
theorem actual_four_rough_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      (∑ k : Fin 4, gamma j N δ (16+k.val)) ≤
        (∑ k : Fin 4, FourPrimeUnit.actualSource N δ (Wu04RemainingCore.row j) (windows j N) k) +
        (∑ k : Fin 4, (roughFamily j N δ k).mass)*
          ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := paid_rough_density hd hh hr (by positivity : 0 < ε/4)
  refine ⟨T,hT,?_⟩
  intro N hN hn j
  have ha (k : Fin 4) := (actual_source_upper j δ k (hT.trans hN) hn).trans
    (add_le_add le_rfl (h N hN hn j k))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun k _ => ha k)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hs
  simpa only [add_assoc, show (4:ℝ)*(ε/4) = ε by ring] using hs

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.actual_four_rough_density
