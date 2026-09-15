import MathlibNt.Wu2008DoubleSieve.GeoMassSelectedFibresBasic

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

/-- The selected coordinate comes first; no sorting or quotient is used. -/
def coordinates (m k : ℕ) :
    (ℝ × (Fin m → ℝ) × (Fin k → ℝ)) ≃ᵐ (Fin (m + (k + 1)) → ℝ) where
  toFun p := Fin.append p.2.1 (Fin.cons p.1 p.2.2)
  invFun x := (x (Fin.natAdd m 0), (fun i => x (Fin.castAdd (k+1) i)),
    fun i => x (Fin.natAdd m i.succ))
  left_inv p := by
    rcases p with ⟨t,l,r⟩
    simp
  right_inv x := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp
    · cases i using Fin.cases <;> simp
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using! (measurable_pi_apply i).comp measurable_snd.fst
    · cases i using Fin.cases with
      | zero => simpa using (measurable_fst : Measurable (fun p :
          ℝ × (Fin m → ℝ) × (Fin k → ℝ) => p.1))
      | succ i => simpa using! (measurable_pi_apply i).comp measurable_snd.snd
  measurable_invFun := by
    exact (measurable_pi_apply _).prodMk
      ((measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
        (measurable_pi_iff.mpr fun _ => measurable_pi_apply _))

theorem coordinates_apply (m k : ℕ) (p : ℝ × (Fin m → ℝ) × (Fin k → ℝ)) :
    coordinates m k p = Fin.append p.2.1 (Fin.cons p.1 p.2.2) := rfl

theorem coordinates_preserving (m k : ℕ) : MeasurePreserving (coordinates m k) := by
  refine ⟨(coordinates m k).measurable, ?_⟩
  change Measure.map (coordinates m k) volume = Measure.pi (fun _ => volume)
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [(coordinates m k).map_apply]
  have he : coordinates m k ⁻¹' univ.pi s =
      s (Fin.natAdd m 0) ×ˢ
      ((univ.pi fun i => s (Fin.castAdd (k+1) i)) ×ˢ
      (univ.pi fun i => s (Fin.natAdd m i.succ))) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, coordinates_apply,
      Fin.forall_fin_add, Fin.forall_fin_succ, Fin.append_left, Fin.append_right,
      Fin.cons_zero, Fin.cons_succ, mem_prod]
    tauto
  simp only [he, Measure.volume_eq_prod, volume_pi, Measure.prod_prod, Measure.pi_pi,
    Fin.prod_univ_add, Fin.prod_univ_succ]
  ac_rfl

theorem coordinates_density (m k : ℕ) (p : ℝ × (Fin m → ℝ) × (Fin k → ℝ)) :
    geometricWeight (Fin.natAdd m (0 : Fin (k+1))) (coordinates m k p) =
      continuousDensity p.2.1 * continuousDensity p.2.2 / p.1^2 := by
  simp only [geometricWeight, coordinates_apply, continuousDensity,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  ring

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
