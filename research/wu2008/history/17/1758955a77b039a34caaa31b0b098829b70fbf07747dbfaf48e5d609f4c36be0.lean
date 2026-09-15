import R2PsiCostsDomains

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Set MeasureTheory LiLiuPrereqBuchstab
open SecondFunctionalJointTail
open scoped BigOperators
noncomputable section

theorem buchstab_below_one {u : ℝ} (hu : u ≤ 1) : buchstab u = 1 := by
  rw [buchstab_eq_approx 0 u (by norm_num; linarith)]
  simp [approx, max_eq_left hu]

theorem buchstab_global_bounds (u : ℝ) : 0 ≤ buchstab u ∧ buchstab u ≤ 1 := by
  by_cases hu : 1 ≤ u
  · exact ⟨buchstab_nonneg hu, buchstab_le_one hu⟩
  · rw [buchstab_below_one (le_of_not_ge hu)]
    norm_num

def zeroBuchstab (u : ℝ) : ℝ := if 1 ≤ u then buchstab u else 0

def fullWeight {n : ℕ} (j : Fin n) (phi : ℝ) (t : Fin n → ℝ) : ℝ :=
  buchstab ((phi - ∑ i, t i) / t j) * geometricWeight j t

def zeroWeight {n : ℕ} (j : Fin n) (phi : ℝ) (t : Fin n → ℝ) : ℝ :=
  zeroBuchstab ((phi - ∑ i, t i) / t j) * geometricWeight j t

theorem fullWeight_formula {n : ℕ} (j : Fin n) (phi : ℝ) (t : Fin n → ℝ) :
    fullWeight j phi t =
      buchstab ((phi - ∑ i, t i) / t j) / (t j * ∏ i, t i) := by
  simp [fullWeight, geometricWeight, continuousDensity, div_eq_mul_inv,
    Finset.prod_inv_distrib, mul_comm, mul_left_comm, mul_assoc]

theorem fullWeight_three (phi : ℝ) (t : Fin 3 → ℝ) :
    fullWeight 1 phi t =
      buchstab ((phi - t 0 - t 1 - t 2) / t 1) /
        (t 0 * t 1 ^ 2 * t 2) := by
  rw [fullWeight_formula]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  congr 2 <;> ring

theorem fullWeight_four (phi : ℝ) (t : Fin 4 → ℝ) :
    fullWeight 2 phi t =
      buchstab ((phi - t 0 - t 1 - t 2 - t 3) / t 2) /
        (t 0 * t 1 * t 2 ^ 2 * t 3) := by
  rw [fullWeight_formula]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  congr 2 <;> ring

theorem fullWeight_five (phi : ℝ) (t : Fin 5 → ℝ) :
    fullWeight 3 phi t =
      buchstab ((phi - t 0 - t 1 - t 2 - t 3 - t 4) / t 3) /
        (t 0 * t 1 * t 2 * t 3 ^ 2 * t 4) := by
  rw [fullWeight_formula]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  congr 2 <;> ring

theorem fullWeight_six (phi : ℝ) (t : Fin 6 → ℝ) :
    fullWeight 4 phi t =
      buchstab ((phi - t 0 - t 1 - t 2 - t 3 - t 4 - t 5) / t 4) /
        (t 0 * t 1 * t 2 * t 3 * t 4 ^ 2 * t 5) := by
  rw [fullWeight_formula]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  congr 2 <;> ring

theorem fullWeight_bounds {n : ℕ} (j : Fin n) (phi : ℝ) {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) :
    0 ≤ fullWeight j phi t ∧ fullWeight j phi t ≤ geometricWeight j t := by
  obtain ⟨hlo, hhi⟩ := buchstab_global_bounds ((phi - ∑ i, t i) / t j)
  have hg := geometricWeight_nonneg j ht
  exact ⟨mul_nonneg hlo hg, mul_le_of_le_one_left hg hhi⟩

theorem fullWeight_measurable {n : ℕ} (j : Fin n) (phi : ℝ) :
    Measurable (fullWeight j phi) := by
  unfold fullWeight geometricWeight continuousDensity
  apply Measurable.mul
  · exact continuous_buchstab.measurable.comp (by fun_prop)
  · fun_prop

theorem fullWeight_integrable {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    IntegrableOn (fullWeight j phi) D := by
  apply (geometricWeight_integrable j hsub).mono'
    (fullWeight_measurable j phi).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hD] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (fullWeight_bounds j phi (hsub ht)).1]
  exact (fullWeight_bounds j phi (hsub ht)).2

theorem fullIntegral_bounds {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    0 ≤ (∫ t in D, fullWeight j phi t) ∧
      (∫ t in D, fullWeight j phi t) ≤ geometricMass j D :=
  ⟨setIntegral_nonneg hD (fun _ ht => (fullWeight_bounds j phi (hsub ht)).1),
    setIntegral_mono_on (fullWeight_integrable j phi hD hsub)
      (geometricWeight_integrable j hsub) hD
      (fun _ ht => (fullWeight_bounds j phi (hsub ht)).2)⟩

theorem zeroWeight_eq_masked {n : ℕ} (j : Fin n) (phi : ℝ)
    {t : Fin n → ℝ} (ht : t ∈ continuousCube n) :
    zeroWeight j phi t = HighNonunitLegal.G j phi t * continuousDensity t := by
  have hp : 0 < t j := by linarith [(ht j (mem_univ j)).1]
  by_cases hl : t ∈ HighNonunitLegal.legal j phi
  · rw [HighNonunitLegal.G_of_legal hl]
    simp only [zeroWeight, zeroBuchstab, if_pos (HighNonunitLegal.argument_ge_one ht hl)]
    unfold geometricWeight
    ring
  · have hu : ¬1 ≤ (phi - ∑ i, t i) / t j := by
      intro hu
      apply hl
      have hh := (le_div_iff₀ hp).1 hu
      change (∑ i, t i) + t j ≤ phi
      linarith
    simp [zeroWeight, zeroBuchstab, hu, HighNonunitLegal.G_of_illegal hl]

theorem fullWeight_split {n : ℕ} (j : Fin n) (phi : ℝ)
    {t : Fin n → ℝ} (ht : t ∈ continuousCube n) :
    fullWeight j phi t = HighNonunitLegal.G j phi t * continuousDensity t +
      (HighNonunitLegal.legal j phi)ᶜ.indicator (geometricWeight j) t := by
  by_cases hl : t ∈ HighNonunitLegal.legal j phi
  · rw [Set.indicator_of_notMem (show t ∉ (HighNonunitLegal.legal j phi)ᶜ from hl),
      add_zero, HighNonunitLegal.G_of_legal hl]
    unfold fullWeight geometricWeight
    ring
  · have hp : 0 < t j := by linarith [(ht j (mem_univ j)).1]
    have hu : (phi - ∑ i, t i) / t j ≤ 1 := by
      apply (div_le_iff₀ hp).2
      have hh : phi < (∑ i, t i) + t j := lt_of_not_ge hl
      linarith
    simp [fullWeight, buchstab_below_one hu, HighNonunitLegal.G_of_illegal hl,
      Set.indicator_of_mem (show t ∈ (HighNonunitLegal.legal j phi)ᶜ from hl)]

def missingMass {n : ℕ} (j : Fin n) (D : Set (Fin n → ℝ)) (phi : ℝ) : ℝ :=
  ∫ t in D \ HighNonunitLegal.legal j phi, geometricWeight j t

theorem fullIntegral_split {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    (∫ t in D, fullWeight j phi t) =
      (∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t) +
        missingMass j D phi := by
  rw [setIntegral_congr_fun hD (fun _ ht => fullWeight_split j phi (hsub ht))]
  rw [integral_add (HighNonunitLegal.weighted_integrable_on j phi hsub)
    ((geometricWeight_integrable j hsub).indicator (HighNonunitLegal.legal_measurable j phi).compl)]
  rw [setIntegral_indicator (HighNonunitLegal.legal_measurable j phi).compl]
  rfl

def K9 (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  ∫ t in (1 / p.kappa1)..(1 / p.kappa3),
    ∫ u in t..(1 / p.kappa3), ∫ v in u..(1 / p.kappa3),
      buchstab ((phi - t - u - v) / u) / (t * u ^ 2 * v)

def lowerK (p : SecondFunctionalParameters) (j : Fin 6) (phi : ℝ) : ℝ :=
  ∫ t in lowerDomain p j, fullWeight 1 phi t

def fourK (p : SecondFunctionalParameters) (j : Fin 4) (phi : ℝ) : ℝ :=
  ∫ t in fourDomain p j, fullWeight 2 phi t

def K20 (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  ∫ t in D20 p, fullWeight 3 phi t

def K21 (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  ∫ t in D21 p, fullWeight 4 phi t

theorem K9_eq (p : SecondFunctionalParameters) (phi : ℝ) :
    K9 p phi = omega3XIntegral p.kappa3 p.kappa1 phi := rfl

theorem lowerK_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) {phi : ℝ} (hphi : 2 ≤ phi) :
    lowerK p j phi = LowerTripleContinuous.K (1 / p.S) (1 / p.kappa1)
      (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) j phi := by
  unfold lowerK
  rw [lowerDomain_eq p hp hs]
  apply setIntegral_congr_fun (LowerTripleContinuous.D_measurable _ _ _ _ _ _)
  intro t ht
  have hl := LowerTripleContinuous.cube_legal hphi
    (LowerTripleContinuous.D_subset_cube
      (LowerTripleContinuous.mother_compact_parameters p hp hs) j ht)
  rw [fullWeight_formula, HighNonunitLegal.weighted_formula hl]

theorem fourK_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) (phi : ℝ) :
    fourK p j phi =
      FourPrimeNonunit.legalK (1 / p.kappa1) (1 / p.kappa2) (1 / p.kappa3)
        (1 / p.s) phi j + missingMass 2 (fourDomain p j) phi := by
  rw [fourK, fullIntegral_split 2 phi (fourDomain_measurable p hp hs j)
    (fourDomain_cube p hp hs j), four_fixed_domain, fourDomain_eq p hp hs]

theorem K20_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    K20 p phi = HighNonunitLegal.K20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi +
      missingMass 3 (D20 p) phi := by
  rw [K20, fullIntegral_split 3 phi (D20_measurable p) (D20_cube p hp hs),
    K20_fixed_domain]
  rfl

theorem K21_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    K21 p phi = HighNonunitLegal.K21 (1 / p.kappa3) (1 / p.s) phi +
      missingMass 4 (D21 p) phi := by
  rw [K21, fullIntegral_split 4 phi (D21_measurable p) (D21_cube p hp hs),
    K21_fixed_domain]
  rfl

end
end WuPaper.R2PsiCosts
