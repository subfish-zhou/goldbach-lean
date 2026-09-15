import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailMass

/-! Uniform weighted transport of the actual Buchstab limit to original domains. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory Filter
open scoped BigOperators Topology

/-- All input is geometric: the actual Buchstab error is supplied internally. -/
theorem weighted_tail_error {n : ℕ} (hn : n ≤ 6) (j : Fin n)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n)
    (m : ℕ) (hm : 3 ≤ m) {phi : ℝ} (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |(∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t) -
      buchstabTailLimit * geometricMass j D| ≤
      (4 / (m.factorial : ℝ)) * geometricMass j D := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (n : ℝ) ≤ 6 := by exact_mod_cast hn
  have hlegal : D ⊆ HighNonunitLegal.legal j phi :=
    hsub.trans (cube_legal j (by linarith))
  have hw := geometricWeight_integrable j hsub
  have hk := HighNonunitLegal.weighted_integrable_on j phi hsub
  have hpw (t : Fin n → ℝ) (ht : t ∈ D) :
      |HighNonunitLegal.G j phi t * continuousDensity t -
        buchstabTailLimit * geometricWeight j t| ≤
      (4 / (m.factorial : ℝ)) * geometricWeight j t := by
    have he : HighNonunitLegal.G j phi t * continuousDensity t -
        buchstabTailLimit * geometricWeight j t =
        (LiLiuPrereqBuchstab.buchstab ((phi - ∑ i, t i) / t j) - buchstabTailLimit) *
          geometricWeight j t := by
      rw [HighNonunitLegal.G_of_legal (hlegal ht)]
      unfold geometricWeight
      ring
    rw [he, abs_mul, abs_of_nonneg (geometricWeight_nonneg j (hsub ht))]
    exact mul_le_mul_of_nonneg_right
      (buchstab_tail_limit_error m hm _
        (argument_ge_six hn j (by positivity) (by linarith) (hsub ht)))
      (geometricWeight_nonneg j (hsub ht))
  calc
    _ = |∫ t in D, (HighNonunitLegal.G j phi t * continuousDensity t -
        buchstabTailLimit * geometricWeight j t)| := by
      rw [integral_sub hk (hw.const_mul _), integral_const_mul]
      rfl
    _ ≤ ∫ t in D, (4 / (m.factorial : ℝ)) * geometricWeight j t := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hw.const_mul _)
      filter_upwards [ae_restrict_mem hD] with t ht
      simpa only [Real.norm_eq_abs] using hpw t ht
    _ = _ := integral_const_mul _ _

/-- The original legal high integral equals the fixed-domain gated integral for every phi. -/
theorem K20_fixed_domain (a2 a3 b phi : ℝ) :
    HighNonunitLegal.K20 a2 a3 b phi =
      ∫ t in massDomain20 a2 a3 b, HighNonunitLegal.G 3 phi t * continuousDensity t :=
  integral_inter_legal 3 phi (massDomain20 a2 a3 b)

theorem K21_fixed_domain (a3 b phi : ℝ) :
    HighNonunitLegal.K21 a3 b phi =
      ∫ t in massDomain21 a3 b, HighNonunitLegal.G 4 phi t * continuousDensity t :=
  integral_inter_legal 4 phi (massDomain21 a3 b)

theorem four_fixed_domain (b c e f phi : ℝ) (j : Fin 4) :
    FourPrimeNonunit.legalK b c e f phi j =
      ∫ t in massDomainFour b c e f j,
        HighNonunitLegal.G 2 phi t * continuousDensity t := by
  have hall : ∀ j : Fin 4, FourPrimeNonunit.legalK b c e f phi j =
      ∫ t in massDomainFour b c e f j,
        HighNonunitLegal.G 2 phi t * continuousDensity t := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact hall j

theorem lower_tail_error (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) (m : ℕ) (hm : 3 ≤ m)
    {phi : ℝ} (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |LowerTripleContinuous.K (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3)
      (1/p.s) j phi - buchstabTailLimit * lowerMass p j| ≤
      (4 / (m.factorial : ℝ)) * lowerMass p j :=
  weighted_tail_error (by omega) 1 (LowerTripleContinuous.D_measurable _ _ _ _ _ j)
    (LowerTripleContinuous.D_subset_cube (LowerTripleContinuous.mother_compact_parameters p hp hs) j)
    m hm hphi

theorem high20_tail_error (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m)
    {phi : ℝ} (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |HighNonunitLegal.K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi -
      buchstabTailLimit * highMass20 p| ≤ (4 / (m.factorial : ℝ)) * highMass20 p := by
  obtain ⟨ha, _, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  rw [K20_fixed_domain]
  exact weighted_tail_error (by omega) 3 (massDomain20_measurable _ _ _)
    (massDomain20_subset_cube ha hb) m hm hphi

theorem high21_tail_error (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m)
    {phi : ℝ} (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |HighNonunitLegal.K21 (1/p.kappa3) (1/p.s) phi -
      buchstabTailLimit * highMass21 p| ≤ (4 / (m.factorial : ℝ)) * highMass21 p := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  rw [K21_fixed_domain]
  exact weighted_tail_error (by omega) 4 (massDomain21_measurable _ _)
    (massDomain21_subset_cube (ha.trans haa) hb) m hm hphi

theorem four_tail_error (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) (m : ℕ) (hm : 3 ≤ m)
    {phi : ℝ} (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |FourPrimeNonunit.legalK (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) phi j -
      buchstabTailLimit * fourMass p j| ≤ (4 / (m.factorial : ℝ)) * fourMass p j := by
  rw [four_fixed_domain]
  exact weighted_tail_error (by omega) 2 (massDomainFour_measurable _ _ _ _ j)
    (massDomainFour_subset_cube (FourPrimeNonunit.legalK_mother_compact p hp hs) j) m hm hphi

/-- Addition preserves original multiplicities and uses one and the same phi. -/
theorem kernel_tail_error (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m)
    {phi : ℝ} (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |SecondFunctionalCoupled.kernel p phi - buchstabTailLimit * M p| ≤
      4 * M p / (m.factorial : ℝ) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  rw [mother_kernel_tail p hp hs (by linarith)]
  have hl := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) =>
    lower_tail_error p hp hs j m hm hphi)
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    four_tail_error p hp hs j m hm hphi)
  have hlabs := (Finset.abs_sum_le_sum_abs
    (fun j : Fin 6 => LowerTripleContinuous.K (1/p.S) (1/p.kappa1) (1/p.kappa2)
      (1/p.kappa3) (1/p.s) j phi - buchstabTailLimit * lowerMass p j) Finset.univ).trans hl
  have hfabs := (Finset.abs_sum_le_sum_abs
    (fun j : Fin 4 => FourPrimeNonunit.legalK (1/p.kappa1) (1/p.kappa2)
      (1/p.kappa3) (1/p.s) phi j - buchstabTailLimit * fourMass p j) Finset.univ).trans hf
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hlabs hfabs
  have h20 := high20_tail_error p hp hs m hm hphi
  have h21 := high21_tail_error p hp hs m hm hphi
  rw [abs_le] at hlabs hfabs h20 h21 ⊢
  unfold M
  simp only [div_eq_mul_inv] at hlabs hfabs h20 h21 ⊢
  constructor <;> nlinarith only [hlabs.1, hlabs.2, hfabs.1, hfabs.2, h20.1, h20.2, h21.1, h21.2]

end Wu2008DoubleSieve.SecondFunctionalJointTail
