import MathlibNt.Wu2008DoubleSieve.SecondFunctionalKernelCompact
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabTailLimit

/-! Actual reciprocal geometric masses, with the selected coordinate retained. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory Filter
open scoped BigOperators Topology

noncomputable def geometricWeight {n : ℕ} (j : Fin n) (t : Fin n → ℝ) : ℝ :=
  continuousDensity t / t j

noncomputable def geometricMass {n : ℕ} (j : Fin n) (D : Set (Fin n → ℝ)) : ℝ :=
  ∫ t in D, geometricWeight j t

theorem geometricWeight_nonneg {n : ℕ} (j : Fin n) {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) : 0 ≤ geometricWeight j t :=
  div_nonneg (continuousDensity_nonneg ht) (by linarith [(ht j (mem_univ j)).1])

theorem geometricWeight_integrable {n : ℕ} (j : Fin n)
    {D : Set (Fin n → ℝ)} (hsub : D ⊆ continuousCube n) :
    IntegrableOn (geometricWeight j) D := by
  have hi : IntegrableOn (fun t : Fin n → ℝ => (1 / t j) * continuousDensity t)
      (continuousCube n) := by
    apply continuousDensity_mul_integrable (K := 10) (by fun_prop)
    intro t ht
    have hj : 0 < t j := by linarith [(ht j (mem_univ j)).1]
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hj)]
    apply (div_le_iff₀ hj).2
    linarith [(ht j (mem_univ j)).1]
  have he : (fun t : Fin n → ℝ => (1 / t j) * continuousDensity t) = geometricWeight j := by
    funext t
    simp [geometricWeight, div_eq_mul_inv, mul_comm]
  rw [he] at hi
  exact hi.mono_set hsub

theorem geometricMass_nonneg {n : ℕ} (j : Fin n) {D : Set (Fin n → ℝ)}
    (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) : 0 ≤ geometricMass j D := by
  exact setIntegral_nonneg hD (fun t ht => geometricWeight_nonneg j (hsub ht))

/-- The fixed original five-dimensional colour/order domain, without a phi gate. -/
def massDomain20 (a2 a3 b : ℝ) : Set (Fin 5 → ℝ) :=
  {t | a2 ≤ t 0 ∧ t 0 ≤ a3 ∧ a3 ≤ t 1 ∧ Monotone t ∧ t 4 ≤ b}

/-- The fixed original six-dimensional weakly ordered domain. -/
def massDomain21 (a3 b : ℝ) : Set (Fin 6 → ℝ) :=
  {t | a3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ b}

theorem massDomain20_measurable (a2 a3 b : ℝ) : MeasurableSet (massDomain20 a2 a3 b) := by
  unfold massDomain20
  rw [← (D20_eq_of_tail (a2 := a2) (a3 := a3) (b := b) le_rfl)]
  exact HighNonunitLegal.D20_measurable a2 a3 b (a3 + 5*b)

theorem massDomain21_measurable (a3 b : ℝ) : MeasurableSet (massDomain21 a3 b) := by
  unfold massDomain21
  rw [← (D21_eq_of_tail (a3 := a3) (b := b) le_rfl)]
  exact HighNonunitLegal.D21_measurable a3 b (7*b)

theorem massDomain20_subset_cube {a2 a3 b : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2) :
    massDomain20 a2 a3 b ⊆ continuousCube 5 := by
  unfold massDomain20
  rw [← (D20_eq_of_tail (a2 := a2) (a3 := a3) (b := b) le_rfl)]
  exact HighNonunitLegal.D20_subset_cube ha hb

theorem massDomain21_subset_cube {a3 b : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2) :
    massDomain21 a3 b ⊆ continuousCube 6 := by
  unfold massDomain21
  rw [← (D21_eq_of_tail (a3 := a3) (b := b) le_rfl)]
  exact HighNonunitLegal.D21_subset_cube ha hb

/-- The four entries are the original domains, not disjointified replacements. -/
def massDomainFour (b c e f : ℝ) : Fin 4 → Set (Fin 4 → ℝ) :=
  ![FourPrimeContinuous.D16 c e, FourPrimeContinuous.D17 c e f,
    FourPrimeContinuous.D18 c e f, FourPrimeContinuous.D19 b c e f]

theorem massDomainFour_measurable (b c e f : ℝ) (j : Fin 4) :
    MeasurableSet (massDomainFour b c e f j) := by
  have hall : ∀ j : Fin 4, MeasurableSet (massDomainFour b c e f j) := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨FourPrimeContinuous.D16_measurable c e,
      FourPrimeContinuous.D17_measurable c e f,
      FourPrimeContinuous.D18_measurable c e f,
      FourPrimeContinuous.D19_measurable b c e f⟩
  exact hall j

theorem massDomainFour_subset_cube {b c e f : ℝ}
    (hp : FourPrimeContinuous.CompactParameters b c e f) (j : Fin 4) :
    massDomainFour b c e f j ⊆ continuousCube 4 := by
  have hall : ∀ j : Fin 4, massDomainFour b c e f j ⊆ continuousCube 4 := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨FourPrimeContinuous.D16_subset_cube hp,
      FourPrimeContinuous.D17_subset_cube hp, FourPrimeContinuous.D18_subset_cube hp,
      FourPrimeContinuous.D19_subset_cube hp⟩
  exact hall j

noncomputable def lowerMass (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  geometricMass 1 (LowerTripleContinuous.D (1/p.S) (1/p.kappa1) (1/p.kappa2)
    (1/p.kappa3) (1/p.s) j)

noncomputable def highMass20 (p : SecondFunctionalParameters) : ℝ :=
  geometricMass 3 (massDomain20 (1/p.kappa2) (1/p.kappa3) (1/p.s))

noncomputable def highMass21 (p : SecondFunctionalParameters) : ℝ :=
  geometricMass 4 (massDomain21 (1/p.kappa3) (1/p.s))

noncomputable def fourMass (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  geometricMass 2 (massDomainFour (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j)

/-- Twelve original geometric integrals. The two unit sections do not enter M. -/
noncomputable def M (p : SecondFunctionalParameters) : ℝ :=
  (∑ j : Fin 6, lowerMass p j) +
    ((highMass20 p + highMass21 p) + ∑ j : Fin 4, fourMass p j)

theorem mother_mass_integrable (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    (∀ j : Fin 6, IntegrableOn (geometricWeight 1)
      (LowerTripleContinuous.D (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j)) ∧
    IntegrableOn (geometricWeight 3) (massDomain20 (1/p.kappa2) (1/p.kappa3) (1/p.s)) ∧
    IntegrableOn (geometricWeight 4) (massDomain21 (1/p.kappa3) (1/p.s)) ∧
    (∀ j : Fin 4, IntegrableOn (geometricWeight 2)
      (massDomainFour (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j)) := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact ⟨fun j => geometricWeight_integrable 1 (LowerTripleContinuous.D_subset_cube
      (LowerTripleContinuous.mother_compact_parameters p hp hs) j),
    geometricWeight_integrable 3 (massDomain20_subset_cube ha hb),
    geometricWeight_integrable 4 (massDomain21_subset_cube (ha.trans haa) hb),
    fun j => geometricWeight_integrable 2 (massDomainFour_subset_cube
      (FourPrimeNonunit.legalK_mother_compact p hp hs) j)⟩

theorem M_nonneg (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : 0 ≤ M p := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have hl (j : Fin 6) : 0 ≤ lowerMass p j := geometricMass_nonneg 1
    (LowerTripleContinuous.D_measurable _ _ _ _ _ j)
    (LowerTripleContinuous.D_subset_cube (LowerTripleContinuous.mother_compact_parameters p hp hs) j)
  have hf (j : Fin 4) : 0 ≤ fourMass p j := geometricMass_nonneg 2
    (massDomainFour_measurable _ _ _ _ j)
    (massDomainFour_subset_cube (FourPrimeNonunit.legalK_mother_compact p hp hs) j)
  exact add_nonneg (Finset.sum_nonneg (fun j _ => hl j))
    (add_nonneg (add_nonneg (geometricMass_nonneg 3 (massDomain20_measurable _ _ _)
      (massDomain20_subset_cube ha hb))
      (geometricMass_nonneg 4 (massDomain21_measurable _ _)
        (massDomain21_subset_cube (ha.trans haa) hb)))
      (Finset.sum_nonneg (fun j _ => hf j)))

end Wu2008DoubleSieve.SecondFunctionalJointTail
