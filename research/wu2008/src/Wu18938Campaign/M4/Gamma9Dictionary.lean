import WR2GammaHighPairGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9OrderedSource
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh Finset
open scoped Classical

theorem gamma9_eq_omega3 {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    gamma j N δ 9 =
      wuOmega3Sum N δ (Wu04RemainingCore.row j).kappa3
        (Wu04RemainingCore.row j).kappa1 (windows j N) := by
  unfold gamma secondFunctionalMotherGammaSum wuOmega3Sum
  apply sum_congr rfl
  intro d hdm
  obtain ⟨hab, hbc, hce, hef⟩ := high_cutoffs j hN hd hh hdm
  rw [secondFunctionalMother_gamma9_ordered_source N d N hab hbc hce hef]
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_s3_orderedTriples_descending N
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
      (fun t => (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℤ)))
  simpa only [Int.cast_sum, Int.cast_natCast, wuOmega3] using h

end Wu18938Campaign.M4
