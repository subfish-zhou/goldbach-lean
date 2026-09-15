import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeRectangleUniform
import Mathlib.MeasureTheory.Integral.Pi

namespace Wu2008DoubleSieve
open Set MeasureTheory
open scoped BigOperators

/-- The literal closed reciprocal cube, including the empty product. -/
def continuousCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (1 / 10 : ℝ) (1 / 2))

/-- The literal reciprocal density; no mass is stipulated. -/
noncomputable def continuousDensity {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∏ i, 1 / t i

theorem continuousCube_measurable (n : ℕ) : MeasurableSet (continuousCube n) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)

theorem continuousDensity_measurable (n : ℕ) :
    Measurable (continuousDensity (n := n)) := by
  unfold continuousDensity
  fun_prop

theorem continuousDensity_nonneg {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) : 0 ≤ continuousDensity t := by
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg zero_le_one (le_trans (by norm_num) (ht i (Set.mem_univ i)).1)

theorem continuousDensity_pos {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) : 0 < continuousDensity t := by
  apply Finset.prod_pos
  intro i _
  apply div_pos zero_lt_one
  have hi := (ht i (Set.mem_univ i)).1
  linarith

theorem continuousReciprocal_integrable {A B : ℝ} (hA : 1 / 10 ≤ A) :
    IntegrableOn (fun t : ℝ => 1 / t) (Icc A B) := by
  apply ContinuousOn.integrableOn_Icc
  exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (by linarith [ht.1]))

theorem continuousDensity_integrable (n : ℕ) :
    IntegrableOn (continuousDensity (n := n)) (continuousCube n) := by
  change Integrable _ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)
  rw [continuousCube, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun _ => continuousReciprocal_integrable (le_refl _))

/-- Bounded measurable multipliers may have either sign. -/
theorem continuousDensity_mul_integrable {n : ℕ} {g : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hg : Measurable g) (hK : ∀ t ∈ continuousCube n, ‖g t‖ ≤ K) :
    IntegrableOn (fun t => g t * continuousDensity t) (continuousCube n) := by
  apply (continuousDensity_integrable n).bdd_mul hg.aestronglyMeasurable
  exact (ae_restrict_mem (continuousCube_measurable n)).mono (fun t ht => hK t ht)

theorem continuousDensity_zero (t : Fin 0 → ℝ) : continuousDensity t = 1 := by
  simp [continuousDensity]

theorem continuousCube_zero : continuousCube 0 = Set.univ := by
  ext t
  simp [continuousCube]

theorem continuousCube_integral_zero :
    ∫ t in continuousCube 0, continuousDensity t = 1 := by
  change (∫ t, continuousDensity t ∂((Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)).restrict _)) = 1
  rw [continuousCube, Measure.restrict_pi_pi]
  unfold continuousDensity
  rw [integral_fintype_prod_eq_prod]
  simp

end Wu2008DoubleSieve
