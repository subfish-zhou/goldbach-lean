import MathlibNt.Wu2008DoubleSieve.SecondFunctionalKernelContinuityBuchstab

/-! The unit integrals have four/five free coordinates, not the five/six
coordinates of the full-dimensional Buchstab terms. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory Filter SecondFunctionalUnitKernel SecondFunctionalUnitFiniteKernel
open scoped BigOperators Topology Classical

/-- Away from its two endpoints, the residual gate is locally stable. -/
theorem unit_F_continuousAt {ell b v : ℝ} (hell : 0 < ell)
    (hlne : ell ≠ v) (hbne : v ≠ b) : ContinuousAt (fun x => F x ell b) v := by
  by_cases hl : ell < v
  · by_cases hb : v < b
    · have hv : v ≠ 0 := ne_of_gt (hell.trans hl)
      apply (continuousAt_const.div continuousAt_id hv).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hl, eventually_lt_nhds hb] with x hx hy
      exact if_pos ⟨hx, hy⟩
    · have hh : b < v := lt_of_le_of_ne (le_of_not_gt hb) hbne.symm
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hh] with x hx
      exact if_neg (fun h => not_lt_of_ge hx.le h.2)
  · have hh : v < ell := lt_of_le_of_ne (le_of_not_gt hl) hlne.symm
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hh] with x hx
    exact if_neg (fun h => not_lt_of_ge hx.le h.1)

/-- Fixed colour/order masks do not add parameter-dependent exceptional faces. -/
theorem unit_G_phi_continuousAt {m r : ℕ} (b phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (flags : Fin r → Bool)
    {t : Fin (m+1) → ℝ} (ht : t ∈ continuousCube (m+1))
    (hl : t (Fin.last m) ≠ phi - ∑ i, t i) (hb : phi - ∑ i, t i ≠ b) :
    ContinuousAt (fun x => G x b C gamma flags t) phi := by
  have hell : 0 < t (Fin.last m) := by linarith [(ht (Fin.last m) (mem_univ _)).1]
  have hF := unit_F_continuousAt hell hl hb
  have hU : ContinuousAt (fun x => U x b t) phi :=
    hF.comp (x := phi) (f := fun x : ℝ => x - ∑ i, t i) (continuousAt_id.sub_const _)
  by_cases hm : mask C gamma flags t
  · simpa only [G, if_pos hm] using hU
  · simpa only [G, if_neg hm] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) phi)

/-- DCT on the positive prefix cube, with the genuine reciprocal majorant. -/
theorem unit_integral_continuous {m r : ℕ} (b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (flags : Fin r → Bool) :
    Continuous (fun phi => ∫ t in continuousCube (m+1),
      G phi b C gamma flags t * continuousDensity t) := by
  rw [continuous_iff_continuousAt]
  intro phi
  apply continuousAt_of_dominated (bound := fun t => 10 * continuousDensity t)
  · exact Eventually.of_forall (fun x => (G_weighted_integrable x b C gamma flags).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro x
    filter_upwards [ae_restrict_mem (continuousCube_measurable (m+1))] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (G_range x b C gamma flags ht).1 (continuousDensity_nonneg ht))]
    exact mul_le_mul_of_nonneg_right (G_range x b C gamma flags ht).2 (continuousDensity_nonneg ht)
  · exact (continuousDensity_integrable (m+1)).const_mul 10
  · filter_upwards [ae_restrict_mem (continuousCube_measurable (m+1)),
      ae_restrict_of_ae (HighUnit.lower_ae (m := m) phi),
      ae_restrict_of_ae (HighUnit.cap_ae (Fin.last m) phi b)] with t ht hl hb
    exact (unit_G_phi_continuousAt b phi C gamma flags ht (hl ht) (hb ht)).mul_const _

/-- Transfer back to the original closed five-coordinate section integral. -/
theorem unit_J20_continuous {a2 a3 b : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2) :
    Continuous (HighUnit.J20 a2 a3 b) := by
  apply (unit_integral_continuous b HighUnit.C20 (HighUnit.gamma20 a2 a3 b) HighUnit.flags20).congr
  intro phi
  exact (HighUnit.J20_identification ha hb phi).symm

/-- Transfer back to the original closed six-coordinate section integral. -/
theorem unit_J21_continuous {a3 b : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2) :
    Continuous (HighUnit.J21 a3 b) := by
  apply (unit_integral_continuous b HighUnit.C21 (HighUnit.gamma21 a3 b) HighUnit.flags21).congr
  intro phi
  exact (HighUnit.J21_identification ha hb phi).symm

end Wu2008DoubleSieve.SecondFunctionalJointTail
