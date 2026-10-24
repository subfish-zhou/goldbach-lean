import WR2GammaHighTailExceptionPayment

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Real Filter
open scoped Classical

/-- Both purification exceptions are paid; the actual rough raw mass is retained. -/
theorem paid_rough_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ k : Bool,
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

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.paid_rough_density
