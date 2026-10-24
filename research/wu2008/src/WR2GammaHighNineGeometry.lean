import WR2GammaHighTheta
import WR2GammaHighPairGeometry
import WR2OmegaHighSwitched
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9IntegralUpper

noncomputable section
namespace WuPaper.R2GammaHigh.GammaNine
open Wu2008DoubleSieve WuSource.SrcSingle HighBoxRecovery Real Finset
open scoped Classical

theorem geometry (j : Fin 3) :
    2 ≤ (Wu04RemainingCore.row j).kappa3 ∧ (Wu04RemainingCore.row j).kappa3 ≤ 3 ∧
    3 ≤ (Wu04RemainingCore.row j).kappa1 ∧ (Wu04RemainingCore.row j).kappa1 ≤ 5 ∧
    (Wu04RemainingCore.row j).kappa3 ≤ (Wu04RemainingCore.row j).kappa1 ∧ True := by
  revert j
  simp only [Wu04RemainingCore.row, ActualNineFeedback.coupledRow,
    SecondFunctionalPositive.parameters, Fin.forall_fin_succ, Fin.forall_fin_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, and_true]
  norm_num [SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
    SecondFunctionalParameters.row4]

theorem weighted_sum (j : Fin 3) (N : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ)*f d) =
      ∑ d ∈ psiPrimes (j.castAdd 4) N, f d :=
  SingleUpperCounts.single_weighted_sum _ _

theorem support_geometry {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    (∀ k p, p ∈ windows j N k → p.Prime ∧ (N : ℝ)^highEta ≤ p) ∧
    (∀ d ∈ boxConvolutionSupport (windows j N), (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) := by
  refine ⟨?_, support_size j hN hd hh⟩
  intro k p hp
  have h := prime_geometry j hN hd hh hp
  exact ⟨h.1,h.2.2.1⟩

theorem theta_total_mass {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      0 ≤ theta j N δ ∧ theta j N δ ≤ 480*truncatedSixthMassScale N := by
  obtain ⟨T,hT,hc⟩ := theta_integral_error (by norm_num : (0:ℝ)<1)
  refine ⟨T,hT,fun N hN he j => ⟨theta_nonneg j (hT.trans hN) hd hh, ?_⟩⟩
  have h := (abs_le.mp (hc N hN he j δ hd.le hh)).2
  have hm := truncatedSixthClosure_scale_nonneg (hT.trans hN)
  have hi := mul_le_mul_of_nonneg_right (prime_integral_bounds j hh).2 hm
  nlinarith only [h,hi,hm]

theorem original_dictionary {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    gamma j N δ 9 = ∑ d ∈ psiPrimes (j.castAdd 4) N,
      wuOmega3 N d δ (Wu04RemainingCore.row j).kappa3 (Wu04RemainingCore.row j).kappa1 := by
  unfold gamma secondFunctionalMotherGammaSum
  rw [← weighted_sum]
  apply sum_congr rfl
  intro d hm
  obtain ⟨hab,hbc,hce,hef⟩ := high_cutoffs j hN hd hh hm
  rw [secondFunctionalMother_gamma9_ordered_source N d N hab hbc hce hef]
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_s3_orderedTriples_descending N (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
      (fun t => (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℤ)))
  simpa only [Int.cast_sum, Int.cast_natCast, wuOmega3] using h

end WuPaper.R2GammaHigh.GammaNine
#print axioms WuPaper.R2GammaHigh.GammaNine.original_dictionary
