import MathlibNt.Wu2008DoubleSieve.GeoMassOrderedBase

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

theorem orderedDomain_closed (n : ℕ) (a b : ℝ) : IsClosed (orderedDomain n a b) := by
  have he : orderedDomain n a b =
      (⋂ i : Fin n, {x | x i ∈ Icc a b}) ∩
      (⋂ i : Fin n, ⋂ k : Fin n, ⋂ (_ : i ≤ k), {x | x i ≤ x k}) := by
    ext x
    simp only [orderedDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, Monotone]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)).inter
    (isClosed_iInter fun i => isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply i) (continuous_apply k))

theorem orderedDomain_measurable (n : ℕ) (a b : ℝ) :
    MeasurableSet (orderedDomain n a b) := (orderedDomain_closed n a b).measurableSet

theorem orderedDomain_subset_rectangle (n : ℕ) (a b : ℝ) :
    orderedDomain n a b ⊆ continuousRectangle (fun _ => a) (fun _ => b) := by
  intro x hx i _
  exact hx.1 i

theorem selected_integrable {n : ℕ} (j : Fin n) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (geometricWeight j) (orderedDomain n a b) :=
  (rectangle_integrable j (fun _ => a) (fun _ => b) (fun _ => ha)).mono_set
    (orderedDomain_subset_rectangle n a b)

theorem pure_integrable (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn continuousDensity (orderedDomain n a b) := by
  have hi : IntegrableOn continuousDensity
      (continuousRectangle (fun _ : Fin n => a) (fun _ => b)) := by
    change Integrable _ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)
    rw [continuousRectangle, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun _ =>
      (continuousOn_const.div continuousOn_id
        (fun x hx => ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc)
  exact hi.mono_set (orderedDomain_subset_rectangle n a b)

theorem pure_zero (a b : ℝ) : pureOrderedMass 0 a b = 1 := by
  have hd : orderedDomain 0 a b = univ := by
    ext x
    simp [orderedDomain, Monotone]
  simp [pureOrderedMass, hd, continuousDensity, Measure.real, volume_pi]

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
