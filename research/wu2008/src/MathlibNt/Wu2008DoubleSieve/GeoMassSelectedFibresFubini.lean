import MathlibNt.Wu2008DoubleSieve.GeoMassSelectedFibresDomain

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

noncomputable def fibreKernel (m k : ℕ) (a b : ℝ)
    (p : ℝ × (Fin m → ℝ) × (Fin k → ℝ)) : ℝ :=
  (Icc a b).indicator (fun t =>
    (orderedDomain m a t).indicator continuousDensity p.2.1 *
    (orderedDomain k t b).indicator continuousDensity p.2.2 / t^2) p.1

theorem coordinates_indicator (m k : ℕ) (a b : ℝ)
    (p : ℝ × (Fin m → ℝ) × (Fin k → ℝ)) :
    (orderedDomain (m+(k+1)) a b).indicator
      (geometricWeight (Fin.natAdd m (0 : Fin (k+1)))) (coordinates m k p) =
    fibreKernel m k a b p := by
  classical
  unfold fibreKernel
  rw [indicator_apply, coordinates_domain]
  by_cases ht : p.1 ∈ Icc a b
  · by_cases hl : p.2.1 ∈ orderedDomain m a p.1
    · by_cases hr : p.2.2 ∈ orderedDomain k p.1 b
      · simp only [ht, hl, hr, and_self, if_true, indicator_of_mem, coordinates_density]
      · simp [ht, hl, hr]
    · simp [ht, hl]
  · simp [ht]

/-- Actual product-space absolute integrability, supplied by the positive rectangle. -/
theorem fibreKernel_integrable (m k : ℕ) {a b : ℝ} (ha : 0 < a) :
    Integrable (fibreKernel m k a b) := by
  have hi := (selected_integrable (Fin.natAdd m (0 : Fin (k+1))) ha).integrable_indicator
    (orderedDomain_measurable _ a b)
  have hc := ((coordinates_preserving m k).integrable_comp_emb
    (coordinates m k).measurableEmbedding).mpr hi
  simpa only [Function.comp_def, coordinates_indicator] using hc

theorem fibreKernel_inner (m k : ℕ) (a b t : ℝ) :
    (∫ q : (Fin m → ℝ) × (Fin k → ℝ), fibreKernel m k a b (t,q)) =
      (Icc a b).indicator (fun t => pureOrderedMass m a t * pureOrderedMass k t b / t^2) t := by
  classical
  by_cases ht : t ∈ Icc a b
  · simp only [fibreKernel, ht, indicator_of_mem]
    rw [integral_div]
    change (∫ q, (orderedDomain m a t).indicator continuousDensity q.1 *
        (orderedDomain k t b).indicator continuousDensity q.2
        ∂((volume : Measure (Fin m → ℝ)).prod volume)) / t^2 = _
    rw [integral_prod_mul, integral_indicator (orderedDomain_measurable m a t),
      integral_indicator (orderedDomain_measurable k t b)]
    rfl
  · simp [fibreKernel, ht]

/-- Absolute integrability of the literal one-dimensional fibre profile. -/
theorem fibre_profile_integrable (m k : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => pureOrderedMass m a t * pureOrderedMass k t b / t^2)
      (Icc a b) := by
  have hi := (fibreKernel_integrable m k (b := b) ha).integral_prod_left
  simp_rw [fibreKernel_inner] at hi
  exact (integrable_indicator_iff measurableSet_Icc).mp hi

/-- The selected fibre identity before the harmless dimension cast. -/
theorem selectedOrderedMass_fibre_add (m k : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    selectedOrderedMass (Fin.natAdd m (0 : Fin (k+1))) a b =
      ∫ t in a..b, pureOrderedMass m a t * pureOrderedMass k t b / t^2 := by
  change (∫ x in orderedDomain (m+(k+1)) a b,
    geometricWeight (Fin.natAdd m (0 : Fin (k+1))) x) = _
  rw [← integral_indicator (orderedDomain_measurable _ a b),
    ← (coordinates_preserving m k).integral_comp']
  simp only [coordinates_indicator]
  rw [show (volume : Measure (ℝ × (Fin m → ℝ) × (Fin k → ℝ))) =
      (volume : Measure ℝ).prod volume from rfl]
  rw [integral_prod _ (fibreKernel_integrable m k ha)]
  simp_rw [fibreKernel_inner]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
