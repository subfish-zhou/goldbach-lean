import Wu04CurvePaid

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalJointTail
open scoped BigOperators
noncomputable section

def D9 (p : SecondFunctionalParameters) : Set (Fin 3 → ℝ) :=
  {t | 1 / p.kappa1 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ 1 / p.kappa3}

def lowerDomain (p : SecondFunctionalParameters) : Fin 6 → Set (Fin 3 → ℝ) :=
  ![{t | 1 / p.kappa1 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ 1 / p.kappa2 ∧
        1 / p.kappa2 ≤ t 2 ∧ t 2 ≤ 1 / p.s},
    {t | 1 / p.kappa1 ≤ t 0 ∧ t 0 ≤ 1 / p.kappa2 ∧
        1 / p.kappa2 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ 1 / p.kappa3},
    {t | 1 / p.S ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ 1 / p.kappa1 ∧
        1 / p.kappa3 ≤ t 2 ∧ t 2 ≤ 1 / p.s},
    {t | 1 / p.S ≤ t 0 ∧ t 0 ≤ 1 / p.kappa1 ∧
        1 / p.kappa1 ≤ t 1 ∧ t 1 ≤ 1 / p.kappa2 ∧
        1 / p.kappa2 ≤ t 2 ∧ t 2 ≤ 1 / p.s},
    {t | 1 / p.S ≤ t 0 ∧ t 0 ≤ 1 / p.kappa1 ∧
        1 / p.kappa2 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ 1 / p.s},
    {t | 1 / p.kappa1 ≤ t 0 ∧ t 0 ≤ 1 / p.kappa2 ∧
        1 / p.kappa2 ≤ t 1 ∧ t 1 ≤ 1 / p.kappa3 ∧
        1 / p.kappa3 ≤ t 2 ∧ t 2 ≤ 1 / p.s}]

def fourDomain (p : SecondFunctionalParameters) : Fin 4 → Set (Fin 4 → ℝ) :=
  ![{t | 1 / p.kappa2 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧
        t 2 ≤ t 3 ∧ t 3 ≤ 1 / p.kappa3},
    {t | 1 / p.kappa2 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧
        t 2 ≤ 1 / p.kappa3 ∧ 1 / p.kappa3 ≤ t 3 ∧ t 3 ≤ 1 / p.s},
    {t | 1 / p.kappa2 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ 1 / p.kappa3 ∧
        1 / p.kappa3 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ 1 / p.s},
    {t | 1 / p.kappa1 ≤ t 0 ∧ t 0 ≤ 1 / p.kappa2 ∧
        1 / p.kappa3 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ 1 / p.s}]

def D20 (p : SecondFunctionalParameters) : Set (Fin 5 → ℝ) :=
  {t | 1 / p.kappa2 ≤ t 0 ∧ t 0 ≤ 1 / p.kappa3 ∧
    1 / p.kappa3 ≤ t 1 ∧ Monotone t ∧ t 4 ≤ 1 / p.s}

def D21 (p : SecondFunctionalParameters) : Set (Fin 6 → ℝ) :=
  {t | 1 / p.kappa3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ 1 / p.s}

theorem lowerDomain_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) :
    lowerDomain p j =
      LowerTripleContinuous.D (1 / p.S) (1 / p.kappa1) (1 / p.kappa2)
        (1 / p.kappa3) (1 / p.s) j := by
  obtain ⟨ha, hab, hbc, hce, hef, hf⟩ :=
    LowerTripleContinuous.mother_compact_parameters p hp hs
  fin_cases j <;> ext t <;>
    simp only [lowerDomain, LowerTripleContinuous.D, LowerTripleGrouped.bands,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Set.mem_setOf_eq] <;> grind

theorem fourDomain_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) :
    fourDomain p j =
      massDomainFour (1 / p.kappa1) (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) j := by
  obtain ⟨hb, hbc, hce, hef, hf⟩ := FourPrimeNonunit.legalK_mother_compact p hp hs
  fin_cases j <;> ext t <;>
    simp only [fourDomain, massDomainFour, FourPrimeContinuous.D16,
      FourPrimeContinuous.D17, FourPrimeContinuous.D18, FourPrimeContinuous.D19,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Set.mem_setOf_eq] <;> grind

theorem D20_eq (p : SecondFunctionalParameters) :
    D20 p = massDomain20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) := rfl

theorem D21_eq (p : SecondFunctionalParameters) :
    D21 p = massDomain21 (1 / p.kappa3) (1 / p.s) := rfl

theorem D9_fibres (p : SecondFunctionalParameters) (t : Fin 3 → ℝ) :
    t ∈ D9 p ↔ t 0 ∈ Icc (1 / p.kappa1) (1 / p.kappa3) ∧
      t 1 ∈ Icc (t 0) (1 / p.kappa3) ∧ t 2 ∈ Icc (t 1) (1 / p.kappa3) := by
  simp only [D9, mem_setOf_eq, mem_Icc]
  grind

theorem lowerDomain_measurable (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    MeasurableSet (lowerDomain p j) := by
  rw [lowerDomain_eq p hp hs]
  exact LowerTripleContinuous.D_measurable _ _ _ _ _ _

theorem lowerDomain_cube (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    lowerDomain p j ⊆ continuousCube 3 := by
  rw [lowerDomain_eq p hp hs]
  exact LowerTripleContinuous.D_subset_cube
    (LowerTripleContinuous.mother_compact_parameters p hp hs) j

theorem fourDomain_measurable (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4) :
    MeasurableSet (fourDomain p j) := by
  rw [fourDomain_eq p hp hs]
  exact massDomainFour_measurable _ _ _ _ _

theorem fourDomain_cube (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4) :
    fourDomain p j ⊆ continuousCube 4 := by
  rw [fourDomain_eq p hp hs]
  exact massDomainFour_subset_cube (FourPrimeNonunit.legalK_mother_compact p hp hs) j

theorem D20_measurable (p : SecondFunctionalParameters) : MeasurableSet (D20 p) :=
  massDomain20_measurable _ _ _

theorem D21_measurable (p : SecondFunctionalParameters) : MeasurableSet (D21 p) :=
  massDomain21_measurable _ _

theorem D20_cube (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : D20 p ⊆ continuousCube 5 := by
  obtain ⟨ha, _, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact massDomain20_subset_cube ha hb

theorem D21_cube (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : D21 p ⊆ continuousCube 6 := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact massDomain21_subset_cube (ha.trans haa) hb

end
end WuPaper.R2PsiCosts
