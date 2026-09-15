import SrcNineRoot

noncomputable section
namespace WuSource.SrcNine.Analytic
open Set MeasureTheory Wu2008DoubleSieve
open scoped BigOperators Interval

def tripleDomain (p : SecondFunctionalParameters) : Fin 6 → Set (Fin 3 → ℝ) :=
  ![{t | 1/p.kappa1 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ 1/p.kappa2 ∧
        1/p.kappa2 ≤ t 2 ∧ t 2 ≤ 1/p.s},
    {t | 1/p.kappa1 ≤ t 0 ∧ t 0 ≤ 1/p.kappa2 ∧ 1/p.kappa2 ≤ t 1 ∧
        t 1 ≤ t 2 ∧ t 2 ≤ 1/p.kappa3},
    {t | 1/p.S ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ 1/p.kappa1 ∧
        1/p.kappa3 ≤ t 2 ∧ t 2 ≤ 1/p.s},
    {t | 1/p.S ≤ t 0 ∧ t 0 ≤ 1/p.kappa1 ∧ 1/p.kappa1 ≤ t 1 ∧
        t 1 ≤ 1/p.kappa2 ∧ 1/p.kappa2 ≤ t 2 ∧ t 2 ≤ 1/p.s},
    {t | 1/p.S ≤ t 0 ∧ t 0 ≤ 1/p.kappa1 ∧ 1/p.kappa2 ≤ t 1 ∧
        t 1 ≤ t 2 ∧ t 2 ≤ 1/p.s},
    {t | 1/p.kappa1 ≤ t 0 ∧ t 0 ≤ 1/p.kappa2 ∧ 1/p.kappa2 ≤ t 1 ∧
        t 1 ≤ 1/p.kappa3 ∧ 1/p.kappa3 ≤ t 2 ∧ t 2 ≤ 1/p.s}]

def fourDomain (p : SecondFunctionalParameters) : Fin 4 → Set (Fin 4 → ℝ) :=
  ![{t | 1/p.kappa2 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧
        t 3 ≤ 1/p.kappa3},
    {t | 1/p.kappa2 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ 1/p.kappa3 ∧
        1/p.kappa3 ≤ t 3 ∧ t 3 ≤ 1/p.s},
    {t | 1/p.kappa2 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ 1/p.kappa3 ∧
        1/p.kappa3 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ 1/p.s},
    {t | 1/p.kappa1 ≤ t 0 ∧ t 0 ≤ 1/p.kappa2 ∧
        1/p.kappa3 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ 1/p.s}]

def fiveDomain (p : SecondFunctionalParameters) : Set (Fin 5 → ℝ) :=
  {t | 1/p.kappa2 ≤ t 0 ∧ t 0 ≤ 1/p.kappa3 ∧ 1/p.kappa3 ≤ t 1 ∧
    Monotone t ∧ t 4 ≤ 1/p.s}

def sixDomain (p : SecondFunctionalParameters) : Set (Fin 6 → ℝ) :=
  {t | 1/p.kappa3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ 1/p.s}

theorem tripleDomain_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) :
    tripleDomain p j =
      LowerTripleContinuous.D (1/p.S) (1/p.kappa1) (1/p.kappa2)
        (1/p.kappa3) (1/p.s) j := by
  have hc := LowerTripleContinuous.mother_compact_parameters p hp hs
  rcases hc with ⟨ha, hab, hbc, hce, hef, hf⟩
  fin_cases j <;> ext t <;>
    dsimp [tripleDomain, LowerTripleContinuous.D, LowerTripleGrouped.bands]
  all_goals constructor <;> intro h <;> repeat' constructor <;> linarith

theorem fourDomain_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) :
    fourDomain p j =
      SecondFunctionalJointTail.massDomainFour (1/p.kappa1) (1/p.kappa2)
        (1/p.kappa3) (1/p.s) j := by
  have hc := FourPrimeNonunit.legalK_mother_compact p hp hs
  rcases hc with ⟨hb, hbc, hce, hef, hf⟩
  fin_cases j <;> ext t <;>
    dsimp [fourDomain, SecondFunctionalJointTail.massDomainFour,
      FourPrimeContinuous.D16, FourPrimeContinuous.D17,
      FourPrimeContinuous.D18, FourPrimeContinuous.D19]
  all_goals constructor <;> intro h <;> repeat' constructor <;> linarith

theorem fiveDomain_eq (p : SecondFunctionalParameters) :
    fiveDomain p =
      SecondFunctionalJointTail.massDomain20 (1/p.kappa2) (1/p.kappa3) (1/p.s) := rfl

theorem sixDomain_eq (p : SecondFunctionalParameters) :
    sixDomain p =
      SecondFunctionalJointTail.massDomain21 (1/p.kappa3) (1/p.s) := rfl

theorem tripleDomain_measurable (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) : MeasurableSet (tripleDomain p j) := by
  rw [tripleDomain_eq p hp hs]
  exact LowerTripleContinuous.D_measurable _ _ _ _ _ _

theorem fourDomain_measurable (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) : MeasurableSet (fourDomain p j) := by
  rw [fourDomain_eq p hp hs]
  exact SecondFunctionalJointTail.massDomainFour_measurable _ _ _ _ _

theorem fiveDomain_measurable (p : SecondFunctionalParameters) :
    MeasurableSet (fiveDomain p) :=
  SecondFunctionalJointTail.massDomain20_measurable _ _ _

theorem sixDomain_measurable (p : SecondFunctionalParameters) :
    MeasurableSet (sixDomain p) :=
  SecondFunctionalJointTail.massDomain21_measurable _ _

theorem tripleDomain_subset_cube (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) : tripleDomain p j ⊆ continuousCube 3 := by
  rw [tripleDomain_eq p hp hs]
  exact LowerTripleContinuous.D_subset_cube
    (LowerTripleContinuous.mother_compact_parameters p hp hs) j

theorem fourDomain_subset_cube (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) : fourDomain p j ⊆ continuousCube 4 := by
  rw [fourDomain_eq p hp hs]
  exact SecondFunctionalJointTail.massDomainFour_subset_cube
    (FourPrimeNonunit.legalK_mother_compact p hp hs) j

theorem fiveDomain_subset_cube (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : fiveDomain p ⊆ continuousCube 5 := by
  obtain ⟨ha, _, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact SecondFunctionalJointTail.massDomain20_subset_cube ha hb

theorem sixDomain_subset_cube (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : sixDomain p ⊆ continuousCube 6 := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact SecondFunctionalJointTail.massDomain21_subset_cube (ha.trans haa) hb

def firstFourInterior : Fin 4 → ℝ := ![401/1000, 402/1000, 403/1000, 404/1000]

theorem first_four_domain_not_all_legal :
    firstFourInterior ∈ fourDomain SecondFunctionalParameters.row1 0 ∧
      firstFourInterior ∉ HighNonunitLegal.legal 2 2 ∧
      (2 - ∑ i, firstFourInterior i) / firstFourInterior 2 = 390/403 := by
  norm_num [firstFourInterior, fourDomain, SecondFunctionalParameters.row1,
    HighNonunitLegal.legal, Fin.sum_univ_succ]
  dsimp only [Matrix.cons_val]
  norm_num

end WuSource.SrcNine.Analytic
