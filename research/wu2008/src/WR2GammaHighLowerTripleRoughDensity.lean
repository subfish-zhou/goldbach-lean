import WR2GammaHighLowerTripleRestrictedDensity
import WR2GammaHighLowerTripleExceptions

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Real Filter
open scoped Classical Topology

/-- Actual high-window Gamma10..15 reach the exact rough main; both exceptions remain explicit. -/
theorem actual_rough_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ k : Fin 6,
      gamma j N δ (10+k.val) ≤ (roughFamily j N δ k).mass*
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
        ε*truncatedSixthMassScale N+
        (max 1 (1/highEta))^3*N*(1+log N)/((N : ℝ)^highEta-1)+
        (max 1 (1/highEta))^4*log N/log 2 := by
  obtain ⟨T1,hT1,h1⟩ := restricted_density hd hh hr he
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : 0 < highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max T1 T2,by omega,fun N hN hEven j k => ?_⟩
  have ha := actual_source_upper j k (by omega) hEven hd hh
  have hb := prime_mass_split (N := N) j k (by omega) hd hh
  have hc := h1 N (by omega) hEven j k profileRough
  have hs := square_mass_bound (N := N) j k (by omega) hd hh (h2 N (by omega))
  have hn := bad_prime_bound (N := N) j k (by omega) hd hh
  change (roughFamily j N δ k).primeMass ≤ (roughFamily j N δ k).mass * _ + _ at hc
  dsimp only [Function.comp_apply] at hs
  linarith only [ha,hb,hc,hs,hn]

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.actual_rough_density
