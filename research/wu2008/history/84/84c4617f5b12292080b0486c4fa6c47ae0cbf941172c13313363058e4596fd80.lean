import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassIntegrability

/-!
# The literal iterated integral and its disjoint split

All integrability hypotheses are discharged for the actual fixed-delta
coefficients before applying Fubini or integral additivity.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def truncatedSixthMassWedgeKernel (δ : ℝ) : (ℝ × ℝ) → ℝ :=
  {v | truncatedSixthLowerWedge δ v.1 v.2}.indicator (truncatedSixthMassAKernel δ)

noncomputable def truncatedSixthMassAdmissibleKernel (δ : ℝ) : (ℝ × ℝ) → ℝ :=
  {v | truncatedSixthLowerAdmissibleRegion δ v.1 v.2}.indicator
    (fun v => truncatedSixthMassAKernel δ v + truncatedSixthMassHKernel δ v)

theorem truncatedSixthMass_integral_eq_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b) :
    (∫ x, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  by_contra h
  exact hx (hs h)

theorem truncatedSixthMass_literal_integrals {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    truncatedSixthLowerFdelta δ = 4 * ∫ v : ℝ × ℝ, truncatedSixthMassAKernel δ v ∧
      truncatedSixthLowerHadmdelta δ = 4 * ∫ v : ℝ × ℝ, truncatedSixthMassHKernel δ v := by
  have hp := truncatedSixthLower_parameters
  have hA : Integrable (truncatedSixthMassAKernel δ) :=
    (truncatedSixthMass_kernels_integrable hδ hδhi).1
  have hH : Integrable (truncatedSixthMassHKernel δ) :=
    (truncatedSixthMass_kernels_integrable hδ hδhi).2
  have hinnerA (x : ℝ) : Function.support (fun y => truncatedSixthMassAKernel δ (x, y)) ⊆
      Icc truncatedSixthLowerBeta truncatedSixthLowerSigma := by
    intro y hy
    by_cases h : truncatedSixthLowerRegion δ x y
    · exact ⟨h.2.2.1, h.2.2.2.1⟩
    · exact False.elim (hy (by simp [truncatedSixthMassAKernel, h]))
  have hinnerH (x : ℝ) : Function.support (fun y => truncatedSixthMassHKernel δ (x, y)) ⊆
      Icc truncatedSixthLowerBeta truncatedSixthLowerSigma := by
    intro y hy
    by_cases h : truncatedSixthLowerAdmissibleRegion δ x y
    · exact ⟨h.1.2.2.1, h.1.2.2.2.1⟩
    · exact False.elim (hy (by simp [truncatedSixthMassHKernel, h]))
  have houterA : Function.support (fun x => ∫ y, truncatedSixthMassAKernel δ (x, y)) ⊆
      Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta := by
    intro x hx
    by_contra h
    apply hx
    change (∫ y, truncatedSixthMassAKernel δ (x, y)) = 0
    have he : (fun y => truncatedSixthMassAKernel δ (x, y)) = 0 := by
      funext y
      have hn : ¬truncatedSixthLowerRegion δ x y := fun hr => h ⟨hr.1, hr.2.1⟩
      simp [truncatedSixthMassAKernel, hn]
    rw [he]
    simp
  have houterH : Function.support (fun x => ∫ y, truncatedSixthMassHKernel δ (x, y)) ⊆
      Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta := by
    intro x hx
    by_contra h
    apply hx
    change (∫ y, truncatedSixthMassHKernel δ (x, y)) = 0
    have he : (fun y => truncatedSixthMassHKernel δ (x, y)) = 0 := by
      funext y
      have hn : ¬truncatedSixthLowerAdmissibleRegion δ x y := fun hr => h ⟨hr.1.1, hr.1.2.1⟩
      simp [truncatedSixthMassHKernel, hn]
    rw [he]
    simp
  constructor
  · rw [show (∫ v : ℝ × ℝ, truncatedSixthMassAKernel δ v) =
        ∫ x, ∫ y, truncatedSixthMassAKernel δ (x, y) from integral_prod _ hA,
      truncatedSixthMass_integral_eq_interval hp.2.1.le houterA]
    simp_rw [truncatedSixthMass_integral_eq_interval hp.2.2.1.le (hinnerA _)]
    rfl
  · rw [show (∫ v : ℝ × ℝ, truncatedSixthMassHKernel δ v) =
        ∫ x, ∫ y, truncatedSixthMassHKernel δ (x, y) from integral_prod _ hH,
      truncatedSixthMass_integral_eq_interval hp.2.1.le houterH]
    simp_rw [truncatedSixthMass_integral_eq_interval hp.2.2.1.le (hinnerH _)]
    rfl

theorem truncatedSixthMass_disjoint_kernel_identity (δ : ℝ) (v : ℝ × ℝ) :
    truncatedSixthMassAKernel δ v + truncatedSixthMassHKernel δ v =
      truncatedSixthMassWedgeKernel δ v + truncatedSixthMassAdmissibleKernel δ v := by
  by_cases hr : truncatedSixthLowerRegion δ v.1 v.2
  · by_cases hy : v.2 ≤ truncatedSixthLowerC δ / 2
    · have ha : truncatedSixthLowerAdmissibleRegion δ v.1 v.2 := ⟨hr, hy⟩
      have hw : ¬truncatedSixthLowerWedge δ v.1 v.2 := fun h => (not_lt_of_ge hy) h.2
      simp [truncatedSixthMassWedgeKernel, truncatedSixthMassAdmissibleKernel, ha, hw]
    · have hw : truncatedSixthLowerWedge δ v.1 v.2 := ⟨hr, lt_of_not_ge hy⟩
      have ha : ¬truncatedSixthLowerAdmissibleRegion δ v.1 v.2 := fun h => hy h.2
      simp [truncatedSixthMassWedgeKernel, truncatedSixthMassAdmissibleKernel,
        truncatedSixthMassHKernel, ha, hw]
  · have ha : ¬truncatedSixthLowerAdmissibleRegion δ v.1 v.2 := fun h => hr h.1
    have hw : ¬truncatedSixthLowerWedge δ v.1 v.2 := fun h => hr h.1
    simp [truncatedSixthMassWedgeKernel, truncatedSixthMassAdmissibleKernel,
      truncatedSixthMassAKernel, truncatedSixthMassHKernel, hr, ha, hw]

theorem truncatedSixthMass_disjoint_integrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    Integrable (truncatedSixthMassWedgeKernel δ) ∧
      Integrable (truncatedSixthMassAdmissibleKernel δ) := by
  have hi := truncatedSixthMass_kernels_integrable hδ hδhi
  have hm := truncatedSixthMass_regions_measurable δ
  exact ⟨hi.1.indicator (hm.1.inter (measurableSet_lt measurable_const measurable_snd)),
    (hi.1.add hi.2).indicator hm.2⟩

theorem truncatedSixthMass_literal_disjoint_integral {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ =
      4 * (∫ v : ℝ × ℝ, truncatedSixthMassWedgeKernel δ v) +
      4 * (∫ v : ℝ × ℝ, truncatedSixthMassAdmissibleKernel δ v) := by
  have hi := truncatedSixthMass_kernels_integrable hδ hδhi
  have hj := truncatedSixthMass_disjoint_integrable hδ hδhi
  rw [(truncatedSixthMass_literal_integrals hδ hδhi).1,
    (truncatedSixthMass_literal_integrals hδ hδhi).2, ← mul_add, ← integral_add hi.1 hi.2]
  simp_rw [truncatedSixthMass_disjoint_kernel_identity]
  rw [integral_add hj.1 hj.2, mul_add]

end Wu2008DoubleSieve
