import Wu18938Campaign.M4.HighRoughPurification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassFinite

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real
open scoped Classical

def originalRoughMass (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ primeTuples N (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s) (word high),
      (((LiLiuPrereqBuchstab.roughNumbers ((N : ℝ) / tupleProduct d t) t.2.1).erase 1).card : ℝ)

theorem original_rough_mass_dictionary (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) :
    ((originalNonunitFamily j N δ high).restrictLabels profileRough).mass =
      originalRoughMass j N δ high := by
  have hd : ∀ d ∈ boxConvolutionSupport (windows j N), 0 < d := by
    intro d hd
    have hdm : d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N := by
      simpa only [support_eq] using hd
    exact (mem_primeWindow.mp hdm).1.pos
  have hh := actualFamily_test_dictionary (N := N) (δ := δ) (Wu04RemainingCore.row j)
    (windows j N) high hd
    (fun x _ => if profileRough x then (convolutionCoeff (windows j N) x.1 : ℝ) else 0)
  have hm : ((originalNonunitFamily j N δ high).restrictLabels profileRough).mass =
      ∑ x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high,
        ∑ _q ∈ actualRawFibre N δ (Wu04RemainingCore.row j) x,
          if profileRough x then (convolutionCoeff (windows j N) x.1 : ℝ) else 0 := by
    rw [← hh]
    simp only [originalNonunitFamily, LabelledPhysical.Family.mass,
      LabelledPhysical.Family.restrictLabels, sum_filter, sum_const, nsmul_eq_mul]
    apply sum_congr rfl
    intro x _
    by_cases hx : profileRough x <;>
      simp [hx, actualFamily, physicalFamily, LabelledPhysical.Family.primes, mul_comm]
  rw [hm]
  exact rough_profiles_dictionary N (windows j N) _ _ _ _ _ _ hd

theorem original_high_gamma_rough_count {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hrho : 0 < ρ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ high : Bool,
      gamma j N δ (if high then 21 else 20) ≤
        originalRoughMass j N δ high *
          (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) +
            ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT, hb⟩ := original_high_gamma_rough_density hd hh hrho heps
  refine ⟨T, hT, ?_⟩
  intro N hN hEven j high
  simpa only [original_rough_mass_dictionary] using hb N hN hEven j high

end Wu18938Campaign.M4
