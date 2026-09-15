import MathlibNt.Wu2008DoubleSieve.FourSeventhsElementaryCap

/-! Actual unit sections and legal nonunit masses: a same-phi support bound.
No published decimal is used, and phi is an arbitrary real number. -/
namespace Wu04HighCoupledSupport
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalJointTail SecondFunctionalGeometricMass
open scoped BigOperators

noncomputable section

theorem legal20_lower {a2 a b phi : ℝ} {t : Fin 5 → ℝ}
    (ht : t ∈ HighNonunitLegal.D20 a2 a b phi) : a2 + 5*a ≤ phi := by
  have h2 := ht.1.2.2.2.1 (show (1 : Fin 5) ≤ 2 by decide)
  have h3 := ht.1.2.2.2.1 (show (1 : Fin 5) ≤ 3 by decide)
  have h4 := ht.1.2.2.2.1 (show (1 : Fin 5) ≤ 4 by decide)
  have hl := ht.2
  change (∑ i, t i) + t 3 ≤ phi at hl
  rw [sum_five] at hl
  linarith [ht.1.1, ht.1.2.2.1]

theorem legal21_lower {a b phi : ℝ} {t : Fin 6 → ℝ}
    (ht : t ∈ HighNonunitLegal.D21 a b phi) : 7*a ≤ phi := by
  have hs : 6*a ≤ ∑ i, t i := by
    calc
      6*a = ∑ _i : Fin 6, a := by simp
      _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ =>
        ht.1.1.trans (ht.1.2.1 (Fin.zero_le i))
  have hj := ht.1.1.trans (ht.1.2.1 (Fin.zero_le (4 : Fin 6)))
  have hl := ht.2
  change (∑ i, t i) + t 4 ≤ phi at hl
  linarith

theorem K20_zero_below {a2 a b phi : ℝ} (hphi : phi < a2 + 5*a) :
    HighNonunitLegal.K20 a2 a b phi = 0 := by
  have he : HighNonunitLegal.D20 a2 a b phi = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact (not_le_of_gt hphi) (legal20_lower ht)
  simp [HighNonunitLegal.K20, he]

theorem K21_zero_below {a b phi : ℝ} (hphi : phi < 7*a) :
    HighNonunitLegal.K21 a b phi = 0 := by
  have he : HighNonunitLegal.D21 a b phi = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact (not_le_of_gt hphi) (legal21_lower ht)
  simp [HighNonunitLegal.K21, he]

theorem J21_zero_below {a b phi : ℝ} (hphi : phi < 6*a) :
    HighUnit.J21 a b phi = 0 := by
  have he (t : Fin 5 → ℝ) : HighUnit.section21 a b phi t = 0 := by
    apply if_neg
    intro ht
    exact (not_le_of_gt hphi) (unit21_support ht).1
  simp only [HighUnit.J21, he, integral_zero]

/-- The omitted reciprocal is bounded only after retaining the full ordered
carrier. The factorial comes from the proved ordered integral, not counting. -/
theorem selected_log_cap {n : ℕ} (j : Fin n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    selectedOrderedMass j a b ≤ Real.log (b/a)^n / ((n.factorial : ℝ)*a) := by
  have h : selectedOrderedMass j a b ≤ (1/a)*pureOrderedMass n a b := by
    unfold selectedOrderedMass geometricMass pureOrderedMass
    rw [← integral_const_mul]
    apply setIntegral_mono_on (SelectedFibres.selected_integrable j ha)
      ((SelectedFibres.pure_integrable n ha).const_mul (1/a))
      (SelectedFibres.orderedDomain_measurable n a b)
    intro t ht
    have hd : 0 ≤ continuousDensity t := Finset.prod_nonneg fun i _ =>
      div_nonneg zero_le_one (ha.trans_le (ht.1 i).1).le
    have hi := one_div_le_one_div_of_le ha (ht.1 j).1
    unfold geometricWeight
    simpa only [div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using
      mul_le_mul_of_nonneg_right hi hd
  rw [OrderedPure.pureOrderedMass_eq_log n ha hab] at h
  convert h using 1
  ring

noncomputable def U20 (p : SecondFunctionalParameters) : ℝ :=
  HighUnitSource.unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s)
noncomputable def U21 (p : SecondFunctionalParameters) : ℝ :=
  HighUnitSource.unitLogCap21 (1/p.kappa3) (1/p.s)
noncomputable def L (p : SecondFunctionalParameters) : ℝ :=
  Real.log ((1/p.s)/(1/p.kappa3))
noncomputable def highKernel (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  HighUnit.J20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi +
  HighUnit.J21 (1/p.kappa3) (1/p.s) phi +
  HighNonunitLegal.K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi +
  HighNonunitLegal.K21 (1/p.kappa3) (1/p.s) phi

/-- Concrete phi-independent majorants for the genuine nonunit integrals. -/
theorem nonunit_log_caps (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    HighNonunitLegal.K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi ≤ U20 p * L p ∧
    HighNonunitLegal.K21 (1/p.kappa3) (1/p.s) phi ≤ U21 p * L p := by
  obtain ⟨ha, haa, hab, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have ha0 : 0 < 1/p.kappa3 := by linarith
  have hlow : 0 ≤ Real.log ((1/p.kappa3)/(1/p.kappa2)) :=
    Real.log_nonneg ((one_le_div (by linarith : 0 < 1/p.kappa2)).2 haa)
  have h20 := selected_log_cap (2 : Fin 4) ha0 hab
  have h21 := selected_log_cap (4 : Fin 6) ha0 hab
  have hm20 := SecondFunctionalFourSevenths.high20_mass_bound p hp hs phi
  have hm21 := SecondFunctionalFourSevenths.high21_mass_bound p hp hs phi
  rw [OriginalBlocks.highMass20_blocks p hp hs] at hm20
  rw [OriginalBlocks.highMass21_blocks p] at hm21
  constructor
  · calc
      _ ≤ Real.log ((1/p.kappa3)/(1/p.kappa2)) *
        (Real.log ((1/p.s)/(1/p.kappa3))^4 / ((4 : ℕ).factorial * (1/p.kappa3))) :=
          hm20.trans (mul_le_mul_of_nonneg_left h20 hlow)
      _ = _ := by norm_num [U20, L, HighUnitSource.unitLogCap20]; ring
  · calc
      _ ≤ Real.log ((1/p.s)/(1/p.kappa3))^6 / ((6 : ℕ).factorial * (1/p.kappa3)) :=
        hm21.trans h21
      _ = _ := by norm_num [U21, L, HighUnitSource.unitLogCap21]; ring

/-- Only elementary window separation; no cost assumptions are stored. -/
def Separated (p : SecondFunctionalParameters) : Prop :=
  1/p.kappa3 + 4*(1/p.s) ≤ 1/p.kappa2 + 5*(1/p.kappa3) ∧
  6*(1/p.s) ≤ 7*(1/p.kappa3)

/-- Three support regimes, with the same arbitrary phi throughout. -/
theorem high_coupled_cap (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (hsep : Separated p) (phi : ℝ) :
    highKernel p phi ≤ max (U20 p) (U20 p * L p + max (U21 p) (U21 p * L p)) := by
  obtain ⟨ha, haa, hab, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have hu20 : HighUnit.J20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi ≤ U20 p :=
    HighUnit.J20_log_cap ha haa hab hb phi
  have hu21 : HighUnit.J21 (1/p.kappa3) (1/p.s) phi ≤ U21 p :=
    HighUnit.J21_log_cap (ha.trans haa) hab hb phi
  obtain ⟨hn20,hn21⟩ := nonunit_log_caps p hp hs phi
  by_cases hfirst : phi < 1/p.kappa2 + 5*(1/p.kappa3)
  · have h20 := K20_zero_below (b := 1/p.s) hfirst
    have h21 := K21_zero_below (b := 1/p.s)
      (show phi < 7*(1/p.kappa3) by linarith)
    have hj21 := J21_zero_below (b := 1/p.s)
      (show phi < 6*(1/p.kappa3) by linarith)
    unfold highKernel
    rw [h20, h21, hj21, add_zero, add_zero, add_zero]
    exact hu20.trans (le_max_left _ _)
  · have hj20 := J20_zero_of_ge ha hb (hsep.1.trans (le_of_not_gt hfirst))
    by_cases hsecond : phi < 7*(1/p.kappa3)
    · have h21 := K21_zero_below (b := 1/p.s) hsecond
      have hh := add_le_add hn20 hu21
      have hm := le_max_left (U21 p) (U21 p * L p)
      have ho := le_max_right (U20 p) (U20 p * L p + max (U21 p) (U21 p * L p))
      unfold highKernel
      rw [hj20, h21]
      linarith only [hh, hm, ho]
    · have hj21 := J21_zero_of_ge (ha.trans haa) hb
        (hsep.2.trans (le_of_not_gt hsecond))
      have hh := add_le_add hn20 hn21
      have hm := le_max_right (U21 p) (U21 p * L p)
      have ho := le_max_right (U20 p) (U20 p * L p + max (U21 p) (U21 p * L p))
      unfold highKernel
      rw [hj20, hj21]
      linarith only [hh, hm, ho]

#print axioms high_coupled_cap
#print axioms selected_log_cap
end
end Wu04HighCoupledSupport
