import MathlibNt.Wu2008DoubleSieve.FourSeventhsLower

namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open Set Real MeasureTheory LiLiuPrereqBuchstab SecondFunctionalJointTail
open SecondFunctionalParameters SecondFunctionalPositive
open scoped BigOperators

/-- The legal gate is retained: its illegal branch contributes zero. -/
theorem weighted_le_geometric {n : ℕ} (j : Fin n) (phi : ℝ) {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) :
    HighNonunitLegal.G j phi t * continuousDensity t ≤ geometricWeight j t := by
  by_cases hl : t ∈ HighNonunitLegal.legal j phi
  · rw [HighNonunitLegal.G_of_legal hl]
    have hb := buchstab_le_one (HighNonunitLegal.argument_ge_one ht hl)
    have hp : 0 < t j := by linarith [(ht j (mem_univ j)).1]
    calc
      _ ≤ (1 / t j) * continuousDensity t := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hb hp.le) (continuousDensity_nonneg ht)
      _ = _ := by unfold geometricWeight; ring
  · rw [HighNonunitLegal.G_of_illegal hl, zero_mul]
    exact geometricWeight_nonneg j ht

/-- Genuine integral monotonicity on an original positive domain. -/
theorem integral_le_geometric {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    (∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t) ≤ geometricMass j D := by
  exact setIntegral_mono_on (HighNonunitLegal.weighted_integrable_on j phi hsub)
    (geometricWeight_integrable j hsub) hD (fun _ ht => weighted_le_geometric j phi (hsub ht))

theorem high20_mass_bound (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    HighNonunitLegal.K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi ≤ highMass20 p := by
  obtain ⟨ha, _, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  rw [K20_fixed_domain]
  exact integral_le_geometric 3 phi (massDomain20_measurable _ _ _)
    (massDomain20_subset_cube ha hb)

theorem high21_mass_bound (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    HighNonunitLegal.K21 (1/p.kappa3) (1/p.s) phi ≤ highMass21 p := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  rw [K21_fixed_domain]
  exact integral_le_geometric 4 phi (massDomain21_measurable _ _)
    (massDomain21_subset_cube (ha.trans haa) hb)

theorem four_mass_bound (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) (j : Fin 4) :
    FourPrimeNonunit.legalK (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) phi j ≤
      fourMass p j := by
  rw [four_fixed_domain]
  exact integral_le_geometric 2 phi (massDomainFour_measurable _ _ _ _ j)
    (massDomainFour_subset_cube (FourPrimeNonunit.legalK_mother_compact p hp hs) j)

/-- Original real masses and original unit logarithmic caps, not existence caps. -/
noncomputable def analyticCap (p : SecondFunctionalParameters) : ℝ :=
  (4/7) * (∑ j : Fin 6, lowerMass p j) + highMass20 p + highMass21 p +
    (∑ j : Fin 4, fourMass p j) +
    HighUnitSource.unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
    HighUnitSource.unitLogCap21 (1/p.kappa3) (1/p.s)

theorem original_mother (i : Fin 4) : (parameters i).MotherAdmissible := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact ⟨row1_motherAdmissible, row2_motherAdmissible, row3_motherAdmissible,
    row4_motherAdmissible⟩

theorem original_s_ge_two (i : Fin 4) : 2 ≤ (parameters i).s := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [row1, row2, row3, row4]

/-- All fourteen terms are compared at the same phi before taking a supremum. -/
theorem original_kernel_bound (i : Fin 4) {phi : ℝ} (hphi : 2 ≤ phi) :
    SecondFunctionalCoupled.kernel (parameters i) phi ≤ analyticCap (parameters i) := by
  have hp := original_mother i
  have hs := original_s_ge_two i
  have hl := original_lower_sum_bound i hphi
  have h20 := high20_mass_bound (parameters i) hp hs phi
  have h21 := high21_mass_bound (parameters i) hp hs phi
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    four_mass_bound (parameters i) hp hs phi j)
  obtain ⟨ha, haa, hab, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have hu20 := HighUnit.J20_log_cap ha haa hab hb phi
  have hu21 := HighUnit.J21_log_cap (ha.trans haa) hab hb phi
  unfold SecondFunctionalCoupled.kernel analyticCap HighUnitSource.unitLogCap20
    HighUnitSource.unitLogCap21
  linarith only [hl, h20, h21, hf, hu20, hu21]

/-- The original unbounded joint supremum, not a sum of separate suprema. -/
theorem original_jointSup_bound (i : Fin 4) :
    SecondFunctionalCoupled.jointSup (parameters i) ≤ analyticCap (parameters i) := by
  apply csSup_le (SecondFunctionalCoupled.values_nonempty (parameters i))
  rintro _ ⟨phi, hphi, rfl⟩
  exact original_kernel_bound i hphi

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
