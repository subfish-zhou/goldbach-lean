import WR2GammaHighCoupledTheta
import WR2GammaHighNineAssembly

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset
open scoped Classical

theorem unpaidTwelve_split (row : Fin 3) (N : ℕ) (δ : ℝ) :
    unpaidTwelve row N δ =
      (∑ k : Fin 6, gamma row N δ (10+k.val)) +
      (∑ k : Fin 4, gamma row N δ (16+k.val)) +
      (gamma row N δ 20 + gamma row N δ 21) := by
  norm_num [unpaidTwelve, Fin.sum_univ_succ, Finset.sum_Icc_succ_top]
  ring

/-- All original Gamma terms have been paid using the same-phi coupled supremum. -/
theorem actual_count_coupled {δ ρ τ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (ht : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      5*psiCount (row.castAdd 4) N ≤
        (classicalEight row + (2/(1-2*δ))*omega3XIntegralEnvelope
          (Wu04RemainingCore.row row).kappa3 (Wu04RemainingCore.row row).kappa1 +
          (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(1+τ)*(2/(1-2*δ))*
            SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row) + ε)*theta row N δ+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT1,h1⟩ := actual_count_with_gamma_nine hd hh (half_pos he)
  obtain ⟨T2,_,h2⟩ := Coupled.actual_twelve_joint_theta hd hh hr ht (half_pos he)
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN hn row
  have ha := h1 N (by omega) hn row
  have hb := h2 N (by omega) hn row
  rw [unpaidTwelve_split] at ha
  have hc := mul_nonneg he.le (theta_nonneg (N := N) row (by omega) hd hh)
  nlinarith only [ha,hb,hc]

end WuPaper.R2GammaHigh
#print axioms WuPaper.R2GammaHigh.actual_count_coupled
