import SrcNineAnalyticSourceDomains

noncomputable section
namespace WuSource.SrcNine.Analytic
open Set MeasureTheory Wu2008DoubleSieve
open scoped BigOperators Interval

def rawWeight {n : ℕ} (j : Fin n) (phi : ℝ) (t : Fin n → ℝ) : ℝ :=
  LiLiuPrereqBuchstab.buchstab ((phi - ∑ i, t i) / t j) / t j *
    continuousDensity t

def rawIntegral {n : ℕ} (j : Fin n) (D : Set (Fin n → ℝ)) (phi : ℝ) : ℝ :=
  ∫ t in D, rawWeight j phi t

def illegalIntegral {n : ℕ} (j : Fin n) (D : Set (Fin n → ℝ)) (phi : ℝ) : ℝ :=
  ∫ t in D \ HighNonunitLegal.legal j phi, rawWeight j phi t

theorem rawWeight_continuousOn {n : ℕ} (j : Fin n) (phi : ℝ) :
    ContinuousOn (rawWeight j phi) (continuousCube n) := by
  have hn (i : Fin n) (t : Fin n → ℝ) (ht : t ∈ continuousCube n) : t i ≠ 0 := by
    have h := (ht i (mem_univ i)).1
    linarith
  have hsum : Continuous (fun t : Fin n → ℝ => phi - ∑ i, t i) := by fun_prop
  have hb := LiLiuPrereqBuchstab.continuous_buchstab.comp_continuousOn
    (hsum.continuousOn.div (continuous_apply j).continuousOn (hn j))
  have hd : ContinuousOn (continuousDensity (n := n)) (continuousCube n) := by
    unfold continuousDensity
    exact continuousOn_finset_prod _ (fun i _ =>
      continuousOn_const.div (continuous_apply i).continuousOn (hn i))
  exact (hb.div (continuous_apply j).continuousOn (hn j)).mul hd

theorem rawWeight_integrable {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : D ⊆ continuousCube n) :
    IntegrableOn (rawWeight j phi) D := by
  have hc : IsCompact (continuousCube n) := isCompact_univ_pi (fun _ => isCompact_Icc)
  exact ((rawWeight_continuousOn j phi).integrableOn_compact hc).mono_set hD

theorem weighted_integral_legal {n : ℕ} (j : Fin n) (phi : ℝ)
    (D : Set (Fin n → ℝ)) :
    (∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t) =
      ∫ t in D ∩ HighNonunitLegal.legal j phi, rawWeight j phi t := by
  rw [← setIntegral_indicator (HighNonunitLegal.legal_measurable j phi)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ HighNonunitLegal.legal j phi
  · simp [rawWeight, HighNonunitLegal.G_of_legal ht, ht]
  · simp [HighNonunitLegal.G_of_illegal ht, ht]

theorem literal_integral_split {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : D ⊆ continuousCube n) :
    (∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t) +
      illegalIntegral j D phi = rawIntegral j D phi := by
  rw [weighted_integral_legal]
  exact integral_inter_add_sdiff (HighNonunitLegal.legal_measurable j phi)
    (rawWeight_integrable j phi hD)

theorem illegalIntegral_zero_of_legal {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : D ⊆ HighNonunitLegal.legal j phi) :
    illegalIntegral j D phi = 0 := by
  simp [illegalIntegral, sdiff_eq_empty.mpr hD]

def rawTriple (p : SecondFunctionalParameters) (j : Fin 6) (phi : ℝ) : ℝ :=
  rawIntegral 1 (tripleDomain p j) phi

def rawFour (p : SecondFunctionalParameters) (j : Fin 4) (phi : ℝ) : ℝ :=
  rawIntegral 2 (fourDomain p j) phi

def rawFive (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  rawIntegral 3 (fiveDomain p) phi

def rawSix (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  rawIntegral 4 (sixDomain p) phi

def illegalFour (p : SecondFunctionalParameters) (j : Fin 4) (phi : ℝ) : ℝ :=
  illegalIntegral 2 (fourDomain p j) phi

def illegalFive (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  illegalIntegral 3 (fiveDomain p) phi

def illegalSix (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  illegalIntegral 4 (sixDomain p) phi

theorem triple_eq_raw (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) (j : Fin 6) :
    LowerTripleContinuous.K (1/p.S) (1/p.kappa1) (1/p.kappa2)
      (1/p.kappa3) (1/p.s) j phi = rawTriple p j phi := by
  have hz := illegalIntegral_zero_of_legal 1 phi
    ((tripleDomain_subset_cube p hp hs j).trans (LowerTripleContinuous.cube_legal hphi))
  have h := literal_integral_split 1 phi (tripleDomain_subset_cube p hp hs j)
  rw [hz, add_zero, tripleDomain_eq p hp hs] at h
  simpa [rawTriple, tripleDomain_eq p hp hs, LowerTripleContinuous.K] using h

theorem four_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) (j : Fin 4) :
    FourPrimeNonunit.legalK (1/p.kappa1) (1/p.kappa2) (1/p.kappa3)
      (1/p.s) phi j + illegalFour p j phi = rawFour p j phi := by
  rw [SecondFunctionalJointTail.four_fixed_domain]
  simpa [illegalFour, rawFour, fourDomain_eq p hp hs] using
    literal_integral_split 2 phi (fourDomain_subset_cube p hp hs j)

theorem five_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    HighNonunitLegal.K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi +
      illegalFive p phi = rawFive p phi := by
  rw [SecondFunctionalJointTail.K20_fixed_domain]
  exact literal_integral_split 3 phi (fiveDomain_subset_cube p hp hs)

theorem six_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    HighNonunitLegal.K21 (1/p.kappa3) (1/p.s) phi +
      illegalSix p phi = rawSix p phi := by
  rw [SecondFunctionalJointTail.K21_fixed_domain]
  exact literal_integral_split 4 phi (sixDomain_subset_cube p hp hs)

theorem rawWeight_literal {n : ℕ} (j : Fin n) (phi : ℝ) (t : Fin n → ℝ) :
    rawWeight j phi t =
      LiLiuPrereqBuchstab.buchstab ((phi - ∑ i, t i) / t j) /
        (t j * ∏ i, t i) := by
  simp only [rawWeight, continuousDensity, div_eq_mul_inv, one_mul,
    Finset.prod_inv_distrib, mul_inv_rev]
  ring

end WuSource.SrcNine.Analytic
