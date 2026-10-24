import WR2GammaHighNineUpper
import WR2GammaHighSignedEight

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Finset
open scoped Classical

def unpaidTwelve (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ i ∈ Icc 10 21, gamma j N δ i

theorem thirteen_split (j : Fin 3) (N : ℕ) (δ : ℝ) :
    unpaidThirteen j N δ = gamma j N δ 9+unpaidTwelve j N δ := by
  unfold unpaidThirteen unpaidTwelve
  norm_num [Finset.sum_Icc_succ_top]
  ring

theorem actual_count_with_gamma_nine {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      5*psiCount (j.castAdd 4) N ≤
        (classicalEight j+(2/(1-2*δ))*omega3XIntegralEnvelope
          (Wu04RemainingCore.row j).kappa3 (Wu04RemainingCore.row j).kappa1+ε)*theta j N δ+
          ε*truncatedSixthMassScale N+unpaidTwelve j N δ := by
  obtain ⟨T1,hT1,h1⟩ := actual_count_partial_eight hd hh (half_pos heps)
  obtain ⟨T2,_,h2⟩ := GammaNine.actual_gamma_nine hd hh (half_pos heps)
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),fun N hN he j => ?_⟩
  have ha := h1 N (by omega) he j
  have hb := h2 N (by omega) he j
  rw [thirteen_split] at ha
  have ht := mul_nonneg heps.le (theta_nonneg (N := N) j (by omega) hd hh)
  nlinarith only [ha,hb,ht]

end WuPaper.R2GammaHigh
#print axioms WuPaper.R2GammaHigh.actual_count_with_gamma_nine
