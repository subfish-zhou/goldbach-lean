import MathlibNt.SieveTheory.LinearSieve.BoundaryMass

/-!
# Regularity of upper Rosser boundary mass

Fixed-depth bounds, integrability, continuity, uniform moduli, and
cell majorants with moving levels and endpoints.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-- The real volume of an interval with positive lower endpoint and upper
endpoint at most one is at most one. -/
private theorem volume_Ioo_real_le_one {a u : ℝ} (ha : 0 < a) (hu : u ≤ 1) :
    MeasureTheory.volume.real (Set.Ioo a u) ≤ 1 := by
  by_cases hau : a < u
  · rw [MeasureTheory.Measure.real_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hau.le)]
    linarith
  · rw [Set.Ioo_eq_empty hau]
    simp

/-- Every fixed-depth boundary mass is uniformly bounded once the recursive
coordinates are bounded away from zero and the inherited upper endpoint is at
most one.  The deliberately coarse bound is stable under the two integrations
in the Rosser recursion. -/
theorem upperRosserBoundaryMassAux_le_inv_sq_pow
    (k : ℕ) {s a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    upperRosserBoundaryMassAux k s a b ≤ (a⁻¹ * a⁻¹) ^ k := by
  induction k generalizing s b with
  | zero =>
      rw [upperRosserBoundaryMassAux_zero]
      split_ifs <;> norm_num
  | succ k ih =>
      rw [upperRosserBoundaryMassAux_succ]
      have haInv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
      have houterUpper : min b (s / 3) ≤ 1 := (min_le_left _ _).trans hb
      have houterMeasure :
          MeasureTheory.volume.real (Set.Ioo a (min b (s / 3))) ≤ 1 :=
        volume_Ioo_real_le_one ha houterUpper
      let F : ℝ → ℝ := fun x₀ => x₀⁻¹ * ∫ (x₁ : ℝ) in Set.Ioo a x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁
      change (∫ x₀ in Set.Ioo a (min b (s / 3)), F x₀) ≤ _
      calc
        (∫ x₀ in Set.Ioo a (min b (s / 3)), F x₀) ≤
            |∫ x₀ in Set.Ioo a (min b (s / 3)), F x₀| := le_abs_self _
        _ ≤ ((a⁻¹ * a⁻¹) ^ (k + 1)) *
              MeasureTheory.volume.real (Set.Ioo a (min b (s / 3))) := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
              (f := F) (C := (a⁻¹ * a⁻¹) ^ (k + 1))
              (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
              (by
                filter_upwards
                    [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
                have hx₀pos : 0 < x₀ := ha.trans hx₀.1
                have hx₀Inv : x₀⁻¹ ≤ a⁻¹ :=
                  (inv_le_inv₀ hx₀pos ha).2 hx₀.1.le
                have hx₀Upper : x₀ ≤ 1 := hx₀.2.le.trans houterUpper
                have hinnerMeasure :
                    MeasureTheory.volume.real (Set.Ioo a x₀) ≤ 1 :=
                  volume_Ioo_real_le_one ha hx₀Upper
                have hinnerNorm :
                    ‖∫ (x₁ : ℝ) in Set.Ioo a x₀,
                        x₁⁻¹ *
                          upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
                      a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
                  calc
                    ‖∫ (x₁ : ℝ) in Set.Ioo a x₀,
                        x₁⁻¹ *
                          upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
                        (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) *
                          MeasureTheory.volume.real (Set.Ioo a x₀) := by
                      apply MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
                      · rw [Real.volume_Ioo]
                        exact ENNReal.ofReal_lt_top
                      · filter_upwards
                          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with
                            x₁ hx₁
                        have hx₁pos : 0 < x₁ := ha.trans hx₁.1
                        have hx₁Inv : x₁⁻¹ ≤ a⁻¹ :=
                          (inv_le_inv₀ hx₁pos ha).2 hx₁.1.le
                        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
                          (inv_nonneg.mpr hx₁pos.le)
                          (upperRosserBoundaryMassAux_nonneg k ha.le))]
                        exact mul_le_mul hx₁Inv
                          (ih (hx₁.2.le.trans hx₀Upper))
                          (upperRosserBoundaryMassAux_nonneg k ha.le) haInv
                    _ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k :=
                      mul_le_of_le_one_right
                        (mul_nonneg haInv
                          (pow_nonneg (mul_nonneg haInv haInv) k))
                        hinnerMeasure
                change ‖x₀⁻¹ * ∫ (x₁ : ℝ) in Set.Ioo a x₀,
                  x₁⁻¹ *
                    upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤ _
                rw [Real.norm_eq_abs, abs_mul,
                  abs_of_pos (inv_pos.mpr hx₀pos)]
                calc
                  x₀⁻¹ * ‖∫ (x₁ : ℝ) in Set.Ioo a x₀,
                      x₁⁻¹ *
                        upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
                      a⁻¹ * (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) :=
                    mul_le_mul hx₀Inv hinnerNorm (norm_nonneg _) haInv
                  _ = (a⁻¹ * a⁻¹) ^ (k + 1) := by
                    rw [pow_succ]
                    ring))
        _ ≤ (a⁻¹ * a⁻¹) ^ (k + 1) :=
          mul_le_of_le_one_right
            (pow_nonneg (mul_nonneg haInv haInv) _) houterMeasure

/-- A common positive lower cutoff gives a uniform fixed-depth bound independent
of all other parameters of the recursive boundary mass. -/
theorem upperRosserBoundaryMassAux_le_of_lower_bound
    (k : ℕ) {s c a b : ℝ} (hc : 0 < c) (hca : c ≤ a) (hb : b ≤ 1) :
    upperRosserBoundaryMassAux k s a b ≤ (c⁻¹ * c⁻¹) ^ k := by
  have ha : 0 < a := hc.trans_le hca
  have haInv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hinv : a⁻¹ ≤ c⁻¹ := (inv_le_inv₀ ha hc).2 hca
  exact (upperRosserBoundaryMassAux_le_inv_sq_pow k ha hb).trans
    (pow_le_pow_left₀ (mul_nonneg haInv haInv)
      (mul_le_mul hinv hinv haInv hcInv) k)

/-- The same recursive bound for the boundary mass with global upper cutoff
one. -/
theorem upperRosserBoundaryMass_le_inv_sq_pow
    (k : ℕ) {s a : ℝ} (ha : 0 < a) :
    upperRosserBoundaryMass k s a ≤ (a⁻¹ * a⁻¹) ^ k :=
  upperRosserBoundaryMassAux_le_inv_sq_pow k ha le_rfl

/-- On a fixed screened interval, the complete outer integrand has a constant
majorant depending only on the depth and the lower endpoint. -/
theorem inv_sq_mul_upperRosserBoundaryMass_le_of_lower_bound
    (k : ℕ) {s a c : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a ≤
      (c⁻¹ * c⁻¹) ^ (k + 1) := by
  have ha : 0 < a := hc.trans_le hca
  have haInv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hinv : a⁻¹ ≤ c⁻¹ := (inv_le_inv₀ ha hc).2 hca
  have hmass :
      upperRosserBoundaryMass k s a ≤ (c⁻¹ * c⁻¹) ^ k :=
    upperRosserBoundaryMassAux_le_of_lower_bound k hc hca le_rfl
  calc
    a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a ≤
        (c⁻¹ * c⁻¹) * (c⁻¹ * c⁻¹) ^ k := by
      apply mul_le_mul
      · exact mul_le_mul hinv hinv haInv hcInv
      · exact hmass
      · exact upperRosserBoundaryMass_nonneg k ha.le
      · exact mul_nonneg hcInv hcInv
    _ = (c⁻¹ * c⁻¹) ^ (k + 1) := by
      rw [pow_succ]
      ring

/-- The inner integrand in the Rosser pair recursion is integrable on every
positive screened interval, at every finite depth. -/
theorem integrableOn_inv_mul_upperRosserBoundaryMassAux
    (k : ℕ) {s a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * upperRosserBoundaryMassAux k (s - x) a x)
      (Set.Ioo a b) := by
  have hfinite : MeasureTheory.volume (Set.Ioo a b) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hmassMeas : MeasureTheory.StronglyMeasurable
      (fun x => upperRosserBoundaryMassAux k (s - x) a x) := by
    have h := (stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable
      (show Measurable (fun x : ℝ => ((s - x, a), x)) by fun_prop)
    convert h using 1
    funext x
    rfl
  have hmeas : MeasureTheory.StronglyMeasurable
      (fun x => x⁻¹ * upperRosserBoundaryMassAux k (s - x) a x) :=
    measurable_id.inv.stronglyMeasurable.mul hmassMeas
  apply MeasureTheory.IntegrableOn.of_bound hfinite hmeas.aestronglyMeasurable
    (a⁻¹ * (a⁻¹ * a⁻¹) ^ k)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  have hxpos : 0 < x := ha.trans hx.1
  have hxinv : x⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hxpos ha).2 hx.1.le
  have hmass := upperRosserBoundaryMassAux_le_inv_sq_pow k
    (s := s - x) (a := a) (b := x) ha (hx.2.le.trans hb)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (inv_nonneg.mpr hxpos.le)
      (upperRosserBoundaryMassAux_nonneg k ha.le))]
  calc
    x⁻¹ * upperRosserBoundaryMassAux k (s - x) a x ≤
        a⁻¹ * upperRosserBoundaryMassAux k (s - x) a x :=
      mul_le_mul_of_nonneg_right hxinv
        (upperRosserBoundaryMassAux_nonneg k ha.le)
    _ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k :=
      mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr ha.le)

/-- The complete fixed-depth Rosser boundary integrand is integrable on every
compact interval bounded away from zero. -/
theorem integrableOn_inv_sq_mul_upperRosserBoundaryMass
    (k : ℕ) (s : ℝ) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn
      (fun a => a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a)
      (Set.Ioo c 1) := by
  have hfinite : MeasureTheory.volume (Set.Ioo c 1) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hmassMeas : MeasureTheory.StronglyMeasurable
      (upperRosserBoundaryMass k s) := by
    have h := (stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable
      (show Measurable (fun a : ℝ => ((s, a), 1)) by fun_prop)
    convert h using 1
    funext a
    rfl
  have hmeas : MeasureTheory.StronglyMeasurable
      (fun a => a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a) :=
    (measurable_id.inv.stronglyMeasurable.mul
      measurable_id.inv.stronglyMeasurable).mul hmassMeas
  apply MeasureTheory.IntegrableOn.of_bound hfinite hmeas.aestronglyMeasurable
    ((c⁻¹ * c⁻¹) ^ (k + 1))
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (inv_nonneg.mpr (hc.trans ha.1).le)
      (inv_nonneg.mpr (hc.trans ha.1).le))
      (upperRosserBoundaryMass_nonneg k (hc.trans ha.1).le))]
  exact inv_sq_mul_upperRosserBoundaryMass_le_of_lower_bound k hc ha.1.le

/-- On every screened compact parameter box, the full three-parameter residual
mass is integrable.  This supplies a common dominated-convergence envelope for
fixed-depth Darboux approximations. -/
theorem integrableOn_upperRosserBoundaryMassAux_compactBox
    (k : ℕ) (s₀ s₁ : ℝ) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn
      (fun p : (ℝ × ℝ) × ℝ =>
        upperRosserBoundaryMassAux k p.1.1 p.1.2 p.2)
      ((Set.Icc s₀ s₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1) := by
  have hcompact :
      IsCompact ((Set.Icc s₀ s₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  apply MeasureTheory.IntegrableOn.of_bound hcompact.measure_lt_top
    (stronglyMeasurable_upperRosserBoundaryMassAux k).aestronglyMeasurable
    ((c⁻¹ * c⁻¹) ^ k)
  filter_upwards
      [MeasureTheory.ae_restrict_mem hcompact.measurableSet] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg
    (upperRosserBoundaryMassAux_nonneg k (hc.le.trans hp.1.2.1))]
  exact upperRosserBoundaryMassAux_le_of_lower_bound
    k hc hp.1.2.1 hp.2.2

/-- The complete outer integrand in one recursive Rosser step is integrable on
every positive screened interval. -/
theorem integrableOn_outer_integrand_upperRosserBoundaryMassAux
    (k : ℕ) {s a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun x₀ => x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁)
      (Set.Ioo a b) := by
  have hfinite : MeasureTheory.volume (Set.Ioo a b) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hinnerMeas : MeasureTheory.StronglyMeasurable
      (fun x₀ => ∫ x₁ in Set.Ioo a x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) := by
    have h :=
      (stronglyMeasurable_integral_inv_mul_upperRosserBoundaryMassAux k).comp_measurable
        (show Measurable (fun x₀ : ℝ => ((s, a), x₀)) by fun_prop)
    convert h using 1
    funext x₀
    rfl
  have hmeas : MeasureTheory.StronglyMeasurable
      (fun x₀ => x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) :=
    measurable_id.inv.stronglyMeasurable.mul hinnerMeas
  apply MeasureTheory.IntegrableOn.of_bound hfinite hmeas.aestronglyMeasurable
    ((a⁻¹ * a⁻¹) ^ (k + 1))
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
  have hx₀pos : 0 < x₀ := ha.trans hx₀.1
  have hx₀inv : x₀⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hx₀pos ha).2 hx₀.1.le
  have hx₀upper : x₀ ≤ 1 := hx₀.2.le.trans hb
  have hinnerNorm :
      ‖∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
        a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
    calc
      ‖∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
          (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) *
            MeasureTheory.volume.real (Set.Ioo a x₀) := by
        apply MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
        · rw [Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top
        · filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
          have hx₁pos : 0 < x₁ := ha.trans hx₁.1
          have hx₁inv : x₁⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hx₁pos ha).2 hx₁.1.le
          have hmass := upperRosserBoundaryMassAux_le_inv_sq_pow k
            (s := s - x₀ - x₁) (a := a) (b := x₁) ha
            (hx₁.2.le.trans hx₀upper)
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (inv_nonneg.mpr hx₁pos.le)
              (upperRosserBoundaryMassAux_nonneg k ha.le))]
          exact (mul_le_mul_of_nonneg_right hx₁inv
            (upperRosserBoundaryMassAux_nonneg k ha.le)).trans
            (mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr ha.le))
      _ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
        have hvol : MeasureTheory.volume.real (Set.Ioo a x₀) ≤ 1 := by
          rw [MeasureTheory.Measure.real_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hx₀.1.le)]
          linarith
        exact mul_le_of_le_one_right
          (mul_nonneg (inv_nonneg.mpr ha.le)
            (pow_nonneg (mul_nonneg (inv_nonneg.mpr ha.le)
              (inv_nonneg.mpr ha.le)) k)) hvol
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hx₀pos)]
  calc
    x₀⁻¹ * ‖∫ x₁ in Set.Ioo a x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
        a⁻¹ * (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) :=
      mul_le_mul hx₀inv hinnerNorm (norm_nonneg _) (inv_nonneg.mpr ha.le)
    _ = (a⁻¹ * a⁻¹) ^ (k + 1) := by
      rw [pow_succ]
      ring

/-- The inner integral in one recursive Rosser pair is bounded uniformly in
the residual level and in every outer coordinate at most `1`. -/
theorem integral_inv_mul_upperRosserBoundaryMassAux_le
    (k : ℕ) {s a x₀ : ℝ} (ha : 0 < a) (hx₀ : x₀ ≤ 1) :
    (∫ x₁ in Set.Ioo a x₀,
     x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) ≤
     a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
  have hnorm :
     ‖∫ x₁ in Set.Ioo a x₀,
         x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
       a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
    calc
     ‖∫ x₁ in Set.Ioo a x₀,
         x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁‖ ≤
         (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) *
           MeasureTheory.volume.real (Set.Ioo a x₀) := by
       apply MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
       · rw [Real.volume_Ioo]
         exact ENNReal.ofReal_lt_top
       · filter_upwards
           [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
         have hx₁pos : 0 < x₁ := ha.trans hx₁.1
         have hx₁inv : x₁⁻¹ ≤ a⁻¹ :=
           (inv_le_inv₀ hx₁pos ha).2 hx₁.1.le
         have hmass := upperRosserBoundaryMassAux_le_inv_sq_pow k
           (s := s - x₀ - x₁) ha (hx₁.2.le.trans hx₀)
         rw [Real.norm_eq_abs, abs_of_nonneg
           (mul_nonneg (inv_nonneg.mpr hx₁pos.le)
             (upperRosserBoundaryMassAux_nonneg k ha.le))]
         exact mul_le_mul hx₁inv hmass
           (upperRosserBoundaryMassAux_nonneg k ha.le) (inv_nonneg.mpr ha.le)
     _ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
       have hvol : MeasureTheory.volume.real (Set.Ioo a x₀) ≤ 1 := by
         rw [MeasureTheory.Measure.real_def, Real.volume_Ioo]
         by_cases hsub : 0 ≤ x₀ - a
         · rw [ENNReal.toReal_ofReal hsub]
           linarith
         · simp [ENNReal.ofReal_eq_zero.mpr (not_le.mp hsub).le]
       exact mul_le_of_le_one_right
         (mul_nonneg (inv_nonneg.mpr ha.le)
           (pow_nonneg (mul_nonneg (inv_nonneg.mpr ha.le)
             (inv_nonneg.mpr ha.le)) k)) hvol
  rw [Real.norm_eq_abs] at hnorm
  exact (le_abs_self _).trans hnorm

/-- Dominated convergence for the inner integral in one Rosser pair.  It is
enough that the residual mass be continuous in its level almost everywhere in
the peeled inner coordinate. -/
theorem continuousAt_integral_inv_mul_upperRosserBoundaryMassAux_level_of_ae
    (k : ℕ) {s a x₀ : ℝ} (ha : 0 < a) (hx₀ : x₀ ≤ 1)
    (hcont : ∀ᵐ x₁ ∂MeasureTheory.volume.restrict (Set.Ioo a x₀),
      ContinuousAt (fun t => upperRosserBoundaryMassAux k t a x₁)
        (s - x₀ - x₁)) :
    ContinuousAt (fun t => ∫ x₁ in Set.Ioo a x₀,
      x₁⁻¹ * upperRosserBoundaryMassAux k (t - x₀ - x₁) a x₁) s := by
  apply MeasureTheory.continuousAt_of_dominated
    (bound := fun _ : ℝ => a⁻¹ * (a⁻¹ * a⁻¹) ^ k)
  · filter_upwards with t
    have hmass := (stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable
      (show Measurable (fun x₁ : ℝ => ((t - x₀ - x₁, a), x₁)) by fun_prop)
    exact
      (measurable_id.inv.stronglyMeasurable.mul hmass).aestronglyMeasurable.mono_measure
        MeasureTheory.Measure.restrict_le_self
  · filter_upwards with t
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
    have hx₁pos : 0 < x₁ := ha.trans hx₁.1
    have hx₁inv : x₁⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hx₁pos ha).2 hx₁.1.le
    have hmass := upperRosserBoundaryMassAux_le_inv_sq_pow k
      (s := t - x₀ - x₁) ha (hx₁.2.le.trans hx₀)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (inv_nonneg.mpr hx₁pos.le) (upperRosserBoundaryMassAux_nonneg k ha.le))]
    exact mul_le_mul hx₁inv hmass
      (upperRosserBoundaryMassAux_nonneg k ha.le) (inv_nonneg.mpr ha.le)
  · exact MeasureTheory.integrableOn_const (by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  · filter_upwards [hcont] with x₁ hx₁
    have hmap : ContinuousAt (fun t : ℝ => t - x₀ - x₁) s := by fun_prop
    have hmass : ContinuousAt
        ((fun r => upperRosserBoundaryMassAux k r a x₁) ∘
          (fun t : ℝ => t - x₀ - x₁)) s :=
      ContinuousAt.comp hx₁ hmap
    exact continuousAt_const.mul (by simpa [Function.comp_def] using hmass)

/-- Dominated convergence for the inner Rosser integral when both the residual
level and the positive lower cutoff vary.  The moving lower face is negligible,
and a fixed half-cutoff supplies an integrable envelope. -/
theorem
    continuousAt_integral_inv_mul_upperRosserBoundaryMassAux_level_lower_of_ae
    (k : ℕ) {s a x₀ : ℝ} (ha : 0 < a) (hx₀ : x₀ ≤ 1)
    (hcont : ∀ᵐ x₁ ∂MeasureTheory.volume.restrict (Set.Iio 1),
      ContinuousAt (fun p : ℝ × ℝ =>
        upperRosserBoundaryMassAux k (p.1 - x₀ - x₁) p.2 x₁) (s, a)) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ x₁ in Set.Ioo p.2 x₀,
      x₁⁻¹ * upperRosserBoundaryMassAux k (p.1 - x₀ - x₁) p.2 x₁) (s, a) := by
  let c := a / 2
  let C := c⁻¹ * (c⁻¹ * c⁻¹) ^ k
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p x₁ =>
    (Set.Ioo p.2 x₀).indicator
      (fun x₁ => x₁⁻¹ *
        upperRosserBoundaryMassAux k (p.1 - x₀ - x₁) p.2 x₁) x₁
  have hc : 0 < c := half_pos ha
  have hcutoff :
      ∀ᶠ p : ℝ × ℝ in nhds (s, a), c < p.2 :=
    continuousAt_snd (Ioi_mem_nhds (by dsimp [c]; linarith))
  have hcont' : ∀ᵐ x₁ ∂MeasureTheory.volume, x₁ ∈ Set.Iio 1 →
      ContinuousAt (fun p : ℝ × ℝ =>
        upperRosserBoundaryMassAux k (p.1 - x₀ - x₁) p.2 x₁) (s, a) := by
    simpa only [MeasureTheory.ae_restrict_iff' measurableSet_Iio] using hcont
  have hF : ContinuousAt (fun p => ∫ x₁, F p x₁) (s, a) := by
    apply MeasureTheory.continuousAt_of_dominated
      (bound := (Set.Ioo c 1).indicator (fun _ : ℝ => C))
    · filter_upwards with p
      have hmass :=
        (stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable
          (show Measurable (fun x₁ : ℝ =>
            ((p.1 - x₀ - x₁, p.2), x₁)) by fun_prop)
      exact
        (measurable_id.inv.stronglyMeasurable.mul hmass).indicator
          measurableSet_Ioo |>.aestronglyMeasurable
    · filter_upwards [hcutoff] with p hp
      filter_upwards with x₁
      by_cases hx : x₁ ∈ Set.Ioo p.2 x₀
      · have hxc : c < x₁ := hp.trans hx.1
        have hmass := upperRosserBoundaryMassAux_le_of_lower_bound
          k (s := p.1 - x₀ - x₁) hc hp.le (hx.2.le.trans hx₀)
        have hxpos : 0 < x₁ := hc.trans hxc
        have hxinv : x₁⁻¹ ≤ c⁻¹ :=
          (inv_le_inv₀ hxpos hc).2 hxc.le
        have hnonneg := upperRosserBoundaryMassAux_nonneg
          k (s := p.1 - x₀ - x₁) (b := x₁) (hc.le.trans hp.le)
        rw [show F p x₁ =
            x₁⁻¹ * upperRosserBoundaryMassAux k
              (p.1 - x₀ - x₁) p.2 x₁ by simp [F, hx],
          Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (inv_nonneg.mpr hxpos.le) hnonneg),
          show (Set.Ioo c 1).indicator (fun _ : ℝ => C) x₁ = C by
            simp [hxc, hx.2.trans_le hx₀]]
        exact mul_le_mul hxinv hmass hnonneg (inv_nonneg.mpr hc.le)
      · rw [show F p x₁ = 0 by simp [F, hx], norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by
          dsimp [C]
          positivity) x₁
    · have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => C) (Set.Ioo c 1) :=
        MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
      exact hconst.integrable_indicator measurableSet_Ioo
    · filter_upwards [hcont', MeasureTheory.volume.ae_ne a,
        MeasureTheory.volume.ae_ne x₀] with x₁ hxcont' hxa hxx₀
      by_cases hx : x₁ ∈ Set.Ioo a x₀
      · have hxone : x₁ ∈ Set.Iio 1 := hx.2.trans_le hx₀
        have hxcont := hxcont' hxone
        have heventually :
            ∀ᶠ p : ℝ × ℝ in nhds (s, a), p.2 < x₁ :=
          continuousAt_snd (Iio_mem_nhds hx.1)
        have hprod : ContinuousAt (fun p : ℝ × ℝ =>
            x₁⁻¹ * upperRosserBoundaryMassAux k
              (p.1 - x₀ - x₁) p.2 x₁) (s, a) :=
          continuousAt_const.mul hxcont
        apply hprod.congr_of_eventuallyEq
        filter_upwards [heventually] with p hp
        have hmem : x₁ ∈ Set.Ioo p.2 x₀ := ⟨hp, hx.2⟩
        simp [F, hmem]
      · have hxleft : x₁ < a ∨ x₀ < x₁ := by
          rcases lt_or_gt_of_ne hxa with hxa' | hax
          · exact Or.inl hxa'
          · rcases lt_or_gt_of_ne hxx₀ with hxx₀' | hx₀x
            · exact (hx ⟨hax, hxx₀'⟩).elim
            · exact Or.inr hx₀x
        rcases hxleft with hxa' | hx₀x
        · have heventually :
              ∀ᶠ p : ℝ × ℝ in nhds (s, a), x₁ < p.2 :=
            continuousAt_snd (Ioi_mem_nhds hxa')
          apply (show (fun p => F p x₁) =ᶠ[nhds (s, a)]
              (fun _ => (0 : ℝ)) by
            filter_upwards [heventually] with p hp
            simp [F, not_lt.mpr hp.le]).continuousAt
        · apply (show (fun p => F p x₁) =ᶠ[nhds (s, a)]
              (fun _ => (0 : ℝ)) by
            filter_upwards with p
            simp [F, not_lt.mpr hx₀x.le]).continuousAt
  convert hF using 1
  funext p
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]

/-- Dominated convergence for one complete Rosser pair when the residual level
and positive lower cutoff vary jointly.  The three moving outer faces are null,
while the preceding inner-integral lemma supplies pointwise continuity. -/
theorem continuousAt_upperRosserBoundaryMassAux_succ_level_lower_of_ae
    (k : ℕ) {s a b : ℝ} (ha : 0 < a) (hb : b ≤ 1)
    (hinner : ∀ᵐ x₀ ∂MeasureTheory.volume.restrict (Set.Iio 1),
      ContinuousAt (fun p : ℝ × ℝ => ∫ x₁ in Set.Ioo p.2 x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k
          (p.1 - x₀ - x₁) p.2 x₁) (s, a)) :
    ContinuousAt
      (fun p : ℝ × ℝ => upperRosserBoundaryMassAux (k + 1) p.1 p.2 b)
      (s, a) := by
  let c := a / 2
  let C := (c⁻¹ * c⁻¹) ^ (k + 1)
  let inner : (ℝ × ℝ) → ℝ → ℝ := fun p x₀ => ∫ x₁ in Set.Ioo p.2 x₀,
    x₁⁻¹ * upperRosserBoundaryMassAux k (p.1 - x₀ - x₁) p.2 x₁
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p x₀ =>
    (Set.Ioo p.2 (min b (p.1 / 3))).indicator
      (fun x₀ => x₀⁻¹ * inner p x₀) x₀
  have hc : 0 < c := half_pos ha
  have hcutoff :
      ∀ᶠ p : ℝ × ℝ in nhds (s, a), c < p.2 :=
    continuousAt_snd (Ioi_mem_nhds (by dsimp [c]; linarith))
  have hinner' : ∀ᵐ x₀ ∂MeasureTheory.volume, x₀ ∈ Set.Iio 1 →
      ContinuousAt (fun p : ℝ × ℝ => ∫ x₁ in Set.Ioo p.2 x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k
          (p.1 - x₀ - x₁) p.2 x₁) (s, a) := by
    simpa only [MeasureTheory.ae_restrict_iff' measurableSet_Iio] using hinner
  have hF : ContinuousAt (fun p => ∫ x₀, F p x₀) (s, a) := by
    apply MeasureTheory.continuousAt_of_dominated
      (bound := (Set.Ioo c 1).indicator (fun _ : ℝ => C))
    · filter_upwards with p
      have hinnerMeas :=
        (stronglyMeasurable_integral_inv_mul_upperRosserBoundaryMassAux k).comp_measurable
          (show Measurable (fun x₀ : ℝ => ((p.1, p.2), x₀)) by fun_prop)
      have hinnerMeas' :
          MeasureTheory.StronglyMeasurable (fun x₀ => inner p x₀) := by
        convert hinnerMeas using 1
        funext x₀
        rfl
      exact
        (measurable_id.inv.stronglyMeasurable.mul hinnerMeas').indicator
          measurableSet_Ioo |>.aestronglyMeasurable
    · filter_upwards [hcutoff] with p hp
      filter_upwards with x₀
      by_cases hx : x₀ ∈ Set.Ioo p.2 (min b (p.1 / 3))
      · have hxc : c < x₀ := hp.trans hx.1
        have hxpos : 0 < x₀ := hc.trans hxc
        have hxupperlt : x₀ < 1 :=
          (hx.2.trans_le (min_le_left _ _)).trans_le hb
        have hxupper : x₀ ≤ 1 := hxupperlt.le
        have hxinv : x₀⁻¹ ≤ c⁻¹ :=
          (inv_le_inv₀ hxpos hc).2 hxc.le
        have hinnerNorm :
            ‖inner p x₀‖ ≤ c⁻¹ * (c⁻¹ * c⁻¹) ^ k := by
          dsimp only [inner]
          calc
            ‖∫ x₁ in Set.Ioo p.2 x₀,
                x₁⁻¹ * upperRosserBoundaryMassAux k
                  (p.1 - x₀ - x₁) p.2 x₁‖ ≤
                (c⁻¹ * (c⁻¹ * c⁻¹) ^ k) *
                  MeasureTheory.volume.real (Set.Ioo p.2 x₀) := by
              apply MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
              · rw [Real.volume_Ioo]
                exact ENNReal.ofReal_lt_top
              · filter_upwards
                  [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
                have hx₁c : c < x₁ := hp.trans hx₁.1
                have hx₁pos : 0 < x₁ := hc.trans hx₁c
                have hx₁inv : x₁⁻¹ ≤ c⁻¹ :=
                  (inv_le_inv₀ hx₁pos hc).2 hx₁c.le
                have hmass := upperRosserBoundaryMassAux_le_of_lower_bound
                  k (s := p.1 - x₀ - x₁) hc hp.le
                    (hx₁.2.le.trans hxupper)
                have hnonneg := upperRosserBoundaryMassAux_nonneg
                  k (s := p.1 - x₀ - x₁) (b := x₁) (hc.le.trans hp.le)
                rw [Real.norm_eq_abs, abs_of_nonneg
                  (mul_nonneg (inv_nonneg.mpr hx₁pos.le) hnonneg)]
                exact mul_le_mul hx₁inv hmass hnonneg (inv_nonneg.mpr hc.le)
            _ ≤ c⁻¹ * (c⁻¹ * c⁻¹) ^ k := by
              apply mul_le_of_le_one_right
              · positivity
              · exact volume_Ioo_real_le_one (hc.trans hp) hxupper
        rw [show F p x₀ = x₀⁻¹ * inner p x₀ by simp [F, hx],
          Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hxpos),
          show (Set.Ioo c 1).indicator (fun _ : ℝ => C) x₀ = C by
            simp [hxc, hxupperlt]]
        calc
          x₀⁻¹ * ‖inner p x₀‖ ≤
              c⁻¹ * (c⁻¹ * (c⁻¹ * c⁻¹) ^ k) :=
            mul_le_mul hxinv hinnerNorm (norm_nonneg _) (inv_nonneg.mpr hc.le)
          _ = C := by
            dsimp [C]
            rw [pow_succ]
            ring
      · rw [show F p x₀ = 0 by simp [F, hx], norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by
          dsimp [C]
          positivity) x₀
    · have hconst : MeasureTheory.IntegrableOn
          (fun _ : ℝ => C) (Set.Ioo c 1) :=
        MeasureTheory.integrableOn_const (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
      exact hconst.integrable_indicator measurableSet_Ioo
    · filter_upwards [hinner', MeasureTheory.volume.ae_ne a,
        MeasureTheory.volume.ae_ne b,
        MeasureTheory.volume.ae_ne (s / 3)] with x₀ hxinner' hxa hxb hxs
      by_cases hx : x₀ ∈ Set.Ioo a (min b (s / 3))
      · have hxb' : x₀ < b := hx.2.trans_le (min_le_left _ _)
        have hxone : x₀ ∈ Set.Iio 1 := hxb'.trans_le hb
        have hxinner := hxinner' hxone
        have hxs' : 3 * x₀ < s := by
          have := hx.2.trans_le (min_le_right _ _)
          linarith
        have hlower :
            ∀ᶠ p : ℝ × ℝ in nhds (s, a), p.2 < x₀ :=
          continuousAt_snd (Iio_mem_nhds hx.1)
        have hlevel :
            ∀ᶠ p : ℝ × ℝ in nhds (s, a), 3 * x₀ < p.1 :=
          continuousAt_fst (Ioi_mem_nhds hxs')
        have hprod : ContinuousAt
            (fun p : ℝ × ℝ => x₀⁻¹ * inner p x₀) (s, a) :=
          continuousAt_const.mul hxinner
        apply hprod.congr_of_eventuallyEq
        filter_upwards [hlower, hlevel] with p hpLower hpLevel
        have hmem : x₀ ∈ Set.Ioo p.2 (min b (p.1 / 3)) := by
          constructor
          · exact hpLower
          · rw [lt_min_iff]
            exact ⟨hxb', by linarith⟩
        simp [F, hmem]
      · have hxoutside : x₀ < a ∨ b < x₀ ∨ s / 3 < x₀ := by
          rcases lt_or_gt_of_ne hxa with hxa' | hax
          · exact Or.inl hxa'
          · rcases lt_or_gt_of_ne hxb with hxb' | hbx
            · rcases lt_or_gt_of_ne hxs with hxs' | hsx
              · exact (hx ⟨hax, lt_min hxb' hxs'⟩).elim
              · exact Or.inr (Or.inr hsx)
            · exact Or.inr (Or.inl hbx)
        rcases hxoutside with hxa' | hxb' | hxs'
        · have heventually :
              ∀ᶠ p : ℝ × ℝ in nhds (s, a), x₀ < p.2 :=
            continuousAt_snd (Ioi_mem_nhds hxa')
          apply (show (fun p => F p x₀) =ᶠ[nhds (s, a)]
              (fun _ => (0 : ℝ)) by
            filter_upwards [heventually] with p hp
            simp [F, not_lt.mpr hp.le]).continuousAt
        · apply (show (fun p => F p x₀) =ᶠ[nhds (s, a)]
              (fun _ => (0 : ℝ)) by
            filter_upwards with p
            simp [F, not_lt.mpr hxb'.le]).continuousAt
        · have heventually :
              ∀ᶠ p : ℝ × ℝ in nhds (s, a), p.1 < 3 * x₀ :=
            continuousAt_fst (Iio_mem_nhds (by linarith))
          apply (show (fun p => F p x₀) =ᶠ[nhds (s, a)]
              (fun _ => (0 : ℝ)) by
            filter_upwards [heventually] with p hp
            have hnot : ¬x₀ < p.1 / 3 := by linarith
            simp [F, hnot]).continuousAt
  apply hF.congr_of_eventuallyEq
  filter_upwards with p
  rw [upperRosserBoundaryMassAux_succ,
    ← MeasureTheory.integral_indicator measurableSet_Ioo]

/-- Every positive-depth recursive Rosser mass is jointly continuous in the
residual level and positive lower cutoff.  At the first positive depth, the two
depth-zero affine jumps occur only on null inner slices; subsequent depths
follow by induction and dominated convergence. -/
theorem continuousAt_upperRosserBoundaryMassAux_level_lower_succ
    (k : ℕ) {s a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    ContinuousAt
      (fun p : ℝ × ℝ => upperRosserBoundaryMassAux (k + 1) p.1 p.2 b)
      (s, a) := by
  induction k generalizing s a b with
  | zero =>
      apply
        continuousAt_upperRosserBoundaryMassAux_succ_level_lower_of_ae 0 ha hb
      filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Iio] with x₀ hx₀
      apply
        continuousAt_integral_inv_mul_upperRosserBoundaryMassAux_level_lower_of_ae
          0 ha hx₀.le
      filter_upwards [
          (MeasureTheory.volume.restrict (Set.Iio 1)).ae_ne (s - x₀),
          (MeasureTheory.volume.restrict (Set.Iio 1)).ae_ne
            (s - x₀ - 3 * a)] with x₁ hxzero hxterminal
      apply continuousAt_upperRosserBoundaryMassAux_zero_affine_level_lower
      · intro h
        apply hxzero
        linarith
      · intro h
        apply hxterminal
        linarith
  | succ k ih =>
      apply
        continuousAt_upperRosserBoundaryMassAux_succ_level_lower_of_ae
          (k + 1) ha hb
      filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Iio] with x₀ hx₀
      apply
        continuousAt_integral_inv_mul_upperRosserBoundaryMassAux_level_lower_of_ae
          (k + 1) ha hx₀.le
      filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Iio] with x₁ hx₁
      have hx₀const :
          ContinuousAt (fun _ : ℝ × ℝ => x₀) (s, a) :=
        continuousAt_const
      have hx₁const :
          ContinuousAt (fun _ : ℝ × ℝ => x₁) (s, a) :=
        continuousAt_const
      have hmap :
          ContinuousAt (fun p : ℝ × ℝ => (p.1 - x₀ - x₁, p.2)) (s, a) :=
        ((continuousAt_fst.sub hx₀const).sub hx₁const).prodMk continuousAt_snd
      exact
        (ih (s := s - x₀ - x₁) (a := a) (b := x₁) ha hx₁.le).comp
          (x := (s, a)) hmap

/-- Positive-depth recursive Rosser mass is jointly continuous in residual level
and lower cutoff on every compact box screened away from zero. -/
theorem continuousOn_upperRosserBoundaryMassAux_level_lower_succ
    (k : ℕ) {b r₀ r₁ c : ℝ} (hb : b ≤ 1) (hc : 0 < c) :
    ContinuousOn
      (fun p : ℝ × ℝ => upperRosserBoundaryMassAux (k + 1) p.1 p.2 b)
      (Set.Icc r₀ r₁ ×ˢ Set.Icc c 1) := by
  intro p hp
  exact
    (continuousAt_upperRosserBoundaryMassAux_level_lower_succ k
      (hc.trans_le hp.2.1) hb).continuousWithinAt

/-- Joint residual-level/lower-cutoff continuity has a uniform modulus on each
compact box screened away from zero. -/
theorem exists_upperRosserBoundaryMassAux_level_lower_modulus_succ
    (k : ℕ) {b r₀ r₁ c ε : ℝ} (hb : b ≤ 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ Set.Icc r₀ r₁ ×ˢ Set.Icc c 1,
      ∀ q ∈ Set.Icc r₀ r₁ ×ˢ Set.Icc c 1, dist p q < δ →
        |upperRosserBoundaryMassAux (k + 1) p.1 p.2 b -
          upperRosserBoundaryMassAux (k + 1) q.1 q.2 b| < ε := by
  have hcompact : IsCompact (Set.Icc r₀ r₁ ×ˢ Set.Icc c 1) :=
    isCompact_Icc.prod isCompact_Icc
  have huniform :=
    hcompact.uniformContinuousOn_of_continuous
      (continuousOn_upperRosserBoundaryMassAux_level_lower_succ k hb hc)
  simpa [Real.dist_eq] using
    (Metric.uniformContinuousOn_iff.mp huniform ε hε)

/-- The outer integral in one Rosser pair is continuous in the residual level
provided its inner integral is almost everywhere continuous there.  The moving
face `x₀ = s / 3` is a singleton and hence does not obstruct dominated
convergence. -/
theorem continuousAt_upperRosserBoundaryMassAux_succ_level_of_ae
    (k : ℕ) {s a b : ℝ} (ha : 0 < a) (hb : b ≤ 1)
    (hinner : ∀ᵐ x₀ ∂MeasureTheory.volume.restrict (Set.Ioo a b),
      ContinuousAt (fun t => ∫ x₁ in Set.Ioo a x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (t - x₀ - x₁) a x₁) s) :
    ContinuousAt (fun t => upperRosserBoundaryMassAux (k + 1) t a b) s := by
  let inner : ℝ → ℝ → ℝ := fun t x₀ => ∫ x₁ in Set.Ioo a x₀,
    x₁⁻¹ * upperRosserBoundaryMassAux k (t - x₀ - x₁) a x₁
  let F : ℝ → ℝ → ℝ := fun t x₀ =>
    (Set.Iio (t / 3)).indicator (fun x₀ => x₀⁻¹ * inner t x₀) x₀
  have hF : ContinuousAt (fun t => ∫ x₀ in Set.Ioo a b, F t x₀) s := by
    apply MeasureTheory.continuousAt_of_dominated
      (bound := fun _ : ℝ => (a⁻¹ * a⁻¹) ^ (k + 1))
    · filter_upwards with t
      have hinnerMeas :=
        (stronglyMeasurable_integral_inv_mul_upperRosserBoundaryMassAux k).comp_measurable
          (show Measurable (fun x₀ : ℝ => ((t, a), x₀)) by fun_prop)
      have hinnerMeas' :
          MeasureTheory.StronglyMeasurable (fun x₀ => inner t x₀) := by
        convert hinnerMeas using 1
        funext x₀
        rfl
      have hmeas : MeasureTheory.StronglyMeasurable
          (fun x₀ => x₀⁻¹ * inner t x₀) :=
        measurable_id.inv.stronglyMeasurable.mul hinnerMeas'
      exact (hmeas.indicator measurableSet_Iio).aestronglyMeasurable.mono_measure
        MeasureTheory.Measure.restrict_le_self
    · filter_upwards with t
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
      by_cases hface : x₀ ∈ Set.Iio (t / 3)
      · rw [show F t x₀ = x₀⁻¹ * inner t x₀ by simp [F, hface]]
        have hx₀pos : 0 < x₀ := ha.trans hx₀.1
        have hx₀inv : x₀⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hx₀pos ha).2 hx₀.1.le
        have hx₀upper : x₀ ≤ 1 := hx₀.2.le.trans hb
        have hinnerNorm :
            ‖inner t x₀‖ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k := by
          dsimp [inner]
          calc
            ‖∫ x₁ in Set.Ioo a x₀,
                x₁⁻¹ * upperRosserBoundaryMassAux k (t - x₀ - x₁) a x₁‖ ≤
                (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) *
                  MeasureTheory.volume.real (Set.Ioo a x₀) := by
              apply MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
              · rw [Real.volume_Ioo]
                exact ENNReal.ofReal_lt_top
              · filter_upwards
                  [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
                have hx₁pos : 0 < x₁ := ha.trans hx₁.1
                have hx₁inv : x₁⁻¹ ≤ a⁻¹ :=
                  (inv_le_inv₀ hx₁pos ha).2 hx₁.1.le
                have hmass := upperRosserBoundaryMassAux_le_inv_sq_pow k
                  (s := t - x₀ - x₁) ha (hx₁.2.le.trans hx₀upper)
                rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
                  (inv_nonneg.mpr hx₁pos.le)
                  (upperRosserBoundaryMassAux_nonneg k ha.le))]
                exact mul_le_mul hx₁inv hmass
                  (upperRosserBoundaryMassAux_nonneg k ha.le)
                  (inv_nonneg.mpr ha.le)
            _ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k :=
              mul_le_of_le_one_right
                (mul_nonneg (inv_nonneg.mpr ha.le)
                  (pow_nonneg (mul_nonneg (inv_nonneg.mpr ha.le)
                    (inv_nonneg.mpr ha.le)) k))
                (volume_Ioo_real_le_one ha hx₀upper)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hx₀pos)]
        calc
          x₀⁻¹ * ‖inner t x₀‖ ≤
              a⁻¹ * (a⁻¹ * (a⁻¹ * a⁻¹) ^ k) :=
            mul_le_mul hx₀inv hinnerNorm (norm_nonneg _) (inv_nonneg.mpr ha.le)
          _ = (a⁻¹ * a⁻¹) ^ (k + 1) := by
            rw [pow_succ]
            ring
      · rw [show F t x₀ = 0 by simp [F, hface], norm_zero]
        positivity
    · exact MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    · filter_upwards [hinner,
        (MeasureTheory.volume.restrict (Set.Ioo a b)).ae_ne (s / 3)] with
          x₀ hxinner hne
      rcases lt_or_gt_of_ne hne with hxs | hsx
      · have hst : 3 * x₀ < s := by linarith
        have heq : (fun t => F t x₀) =ᶠ[nhds s]
            (fun t => x₀⁻¹ * inner t x₀) := by
          filter_upwards [lt_mem_nhds hst] with t ht
          have hxt : x₀ < t / 3 := by linarith
          simp [F, hxt]
        exact (continuousAt_const.mul hxinner).congr_of_eventuallyEq heq
      · have hst : s < 3 * x₀ := by linarith
        apply (show (fun t => F t x₀) =ᶠ[nhds s] (fun _ => (0 : ℝ)) by
          filter_upwards [eventually_lt_nhds hst] with t ht
          have hxt : ¬x₀ < t / 3 := by linarith
          simp [F, hxt]).continuousAt
  exact hF.congr_of_eventuallyEq (by
    filter_upwards with t
    rw [upperRosserBoundaryMassAux_succ,
      MeasureTheory.setIntegral_indicator measurableSet_Iio, Set.Ioo_inter_Iio])

/-- Every positive-depth recursive Rosser boundary mass is continuous in its
residual level.  At depth zero there are two affine jumps; after one peeled
pair, both jumps lie on null one-dimensional slices and dominated convergence
smooths them. -/
theorem continuous_upperRosserBoundaryMassAux_level_succ
    (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    Continuous (fun s => upperRosserBoundaryMassAux (k + 1) s a b) := by
  induction k generalizing a b with
  | zero =>
      rw [continuous_iff_continuousAt]
      intro s
      apply continuousAt_upperRosserBoundaryMassAux_succ_level_of_ae 0 ha hb
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
      apply continuousAt_integral_inv_mul_upperRosserBoundaryMassAux_level_of_ae
        0 ha (hx₀.2.le.trans hb)
      filter_upwards [
          (MeasureTheory.volume.restrict (Set.Ioo a x₀)).ae_ne (s - x₀),
          (MeasureTheory.volume.restrict (Set.Ioo a x₀)).ae_ne
            (s - x₀ - 3 * a)] with x₁ hx₁zero hx₁terminal
      apply continuousAt_upperRosserBoundaryMassAux_zero_level
      · intro h
        apply hx₁zero
        linarith
      · intro h
        apply hx₁terminal
        linarith
  | succ k ih =>
      rw [continuous_iff_continuousAt]
      intro s
      apply
        continuousAt_upperRosserBoundaryMassAux_succ_level_of_ae (k + 1) ha hb
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
      apply continuousAt_integral_inv_mul_upperRosserBoundaryMassAux_level_of_ae
        (k + 1) ha (hx₀.2.le.trans hb)
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
      exact (ih ha (hx₁.2.le.trans (hx₀.2.le.trans hb))).continuousAt

/-- The inner integral in one Rosser pair is jointly continuous in the residual
level and the peeled outer coordinate once the residual boundary mass has
positive depth.  Clipping the moving upper face at `1` gives a global dominated
convergence argument whose restriction is the desired ordered integral. -/
theorem continuousOn_integral_inv_mul_upperRosserBoundaryMassAux_outer_succ
    (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ x₁ in Set.Ioo a p.2,
      x₁⁻¹ * upperRosserBoundaryMassAux (k + 1) (p.1 - p.2 - x₁) a x₁)
      (Set.univ ×ˢ Set.Icc a 1) := by
  let C := a⁻¹ * (a⁻¹ * a⁻¹) ^ (k + 1)
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p x₁ =>
    (Set.Ioo a (min p.2 1)).indicator
      (fun x₁ => x₁⁻¹ *
       upperRosserBoundaryMassAux (k + 1) (p.1 - p.2 - x₁) a x₁) x₁
  have hF : Continuous (fun p => ∫ x₁, F p x₁) := by
    rw [continuous_iff_continuousAt]
    intro p₀
    apply MeasureTheory.continuousAt_of_dominated
      (bound := (Set.Ioo a 1).indicator (fun _ : ℝ => C))
    · filter_upwards with p
      have hmass :=
       (stronglyMeasurable_upperRosserBoundaryMassAux (k + 1)).comp_measurable
         (show Measurable (fun x₁ : ℝ => ((p.1 - p.2 - x₁, a), x₁)) by fun_prop)
      exact
       (measurable_id.inv.stronglyMeasurable.mul hmass).indicator
         measurableSet_Ioo |>.aestronglyMeasurable
    · filter_upwards with p
      filter_upwards with x₁
      by_cases hx : x₁ ∈ Set.Ioo a (min p.2 1)
      · have hxpos : 0 < x₁ := ha.trans hx.1
        have hxoneLt : x₁ < 1 := hx.2.trans_le (min_le_right _ _)
        have hxone : x₁ ≤ 1 := hxoneLt.le
        have hxinv : x₁⁻¹ ≤ a⁻¹ :=
          (inv_le_inv₀ hxpos ha).2 hx.1.le
        have hmass := upperRosserBoundaryMassAux_le_inv_sq_pow (k + 1)
          (s := p.1 - p.2 - x₁) ha hxone
        have hnonneg := upperRosserBoundaryMassAux_nonneg
          (k + 1) (s := p.1 - p.2 - x₁) (b := x₁) ha.le
        rw [show F p x₁ = x₁⁻¹ * upperRosserBoundaryMassAux (k + 1)
              (p.1 - p.2 - x₁) a x₁ by simp [F, hx],
          Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (inv_nonneg.mpr hxpos.le) hnonneg),
          show (Set.Ioo a 1).indicator (fun _ : ℝ => C) x₁ = C by
            simp [hx.1, hxoneLt]]
        exact mul_le_mul hxinv hmass hnonneg (inv_nonneg.mpr ha.le)
      · rw [show F p x₁ = 0 by simp [F, hx], norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by
          dsimp [C]
          positivity) x₁
    · have hconst : MeasureTheory.IntegrableOn
         (fun _ : ℝ => C) (Set.Ioo a 1) :=
       MeasureTheory.integrableOn_const (by
         rw [Real.volume_Ioo]
         exact ENNReal.ofReal_ne_top)
      exact hconst.integrable_indicator measurableSet_Ioo
    · filter_upwards [MeasureTheory.volume.ae_ne (min p₀.2 1)] with x₁ hne
      by_cases hx : x₁ ∈ Set.Ioo a (min p₀.2 1)
      · have hxone : x₁ ≤ 1 := hx.2.le.trans (min_le_right _ _)
        have hmap : ContinuousAt
            (fun p : ℝ × ℝ => p.1 - p.2 - x₁) p₀ := by fun_prop
        have hmass : ContinuousAt
            (fun p : ℝ × ℝ => upperRosserBoundaryMassAux (k + 1)
              (p.1 - p.2 - x₁) a x₁) p₀ :=
          (continuous_upperRosserBoundaryMassAux_level_succ k ha hxone).continuousAt.comp
            hmap
        have hprod : ContinuousAt (fun p : ℝ × ℝ => x₁⁻¹ *
            upperRosserBoundaryMassAux (k + 1) (p.1 - p.2 - x₁) a x₁) p₀ :=
          continuousAt_const.mul hmass
        have heventually : ∀ᶠ p in nhds p₀, x₁ < min p.2 1 :=
          (continuousAt_snd.min continuousAt_const) (Ioi_mem_nhds hx.2)
        apply hprod.congr_of_eventuallyEq
        filter_upwards [heventually] with p hp
        have hmem : x₁ ∈ Set.Ioo a (min p.2 1) := ⟨hx.1, hp⟩
        simp [F, hmem]
      · rcases le_or_gt x₁ a with hxa | hax
        · apply (show (fun p => F p x₁) =ᶠ[nhds p₀] (fun _ => (0 : ℝ)) by
            filter_upwards with p
            simp [F, not_lt.mpr hxa]).continuousAt
        · have hupperle : min p₀.2 1 ≤ x₁ := by
            by_contra hnot
            exact hx ⟨hax, lt_of_not_ge hnot⟩
          have hupper : min p₀.2 1 < x₁ := hupperle.lt_of_ne hne.symm
          have heventually : ∀ᶠ p in nhds p₀, min p.2 1 < x₁ :=
            (continuousAt_snd.min continuousAt_const) (Iio_mem_nhds hupper)
          apply (show (fun p => F p x₁) =ᶠ[nhds p₀] (fun _ => (0 : ℝ)) by
            filter_upwards [heventually] with p hp
            simp [F, not_lt.mpr hp.le]).continuousAt
  apply hF.continuousOn.congr
  intro p hp
  change (∫ x₁ in Set.Ioo a p.2,
      x₁⁻¹ * upperRosserBoundaryMassAux (k + 1) (p.1 - p.2 - x₁) a x₁) =
    ∫ x₁, (Set.Ioo a (min p.2 1)).indicator
      (fun x₁ => x₁⁻¹ * upperRosserBoundaryMassAux (k + 1)
       (p.1 - p.2 - x₁) a x₁) x₁
  rw [show min p.2 1 = p.2 by exact min_eq_left hp.2.2]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]

/-- On compact level and outer-coordinate ranges, the positive-depth inner
Rosser integral has a uniform modulus. -/
theorem exists_integral_inv_mul_upperRosserBoundaryMassAux_outer_modulus_succ
    (k : ℕ) {s₀ s₁ a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ Set.Icc s₀ s₁ ×ˢ Set.Icc a 1,
      ∀ q ∈ Set.Icc s₀ s₁ ×ˢ Set.Icc a 1, dist p q < δ →
       |(∫ x₁ in Set.Ioo a p.2,
             x₁⁻¹ * upperRosserBoundaryMassAux (k + 1)
               (p.1 - p.2 - x₁) a x₁) -
         ∫ x₁ in Set.Ioo a q.2,
             x₁⁻¹ * upperRosserBoundaryMassAux (k + 1)
               (q.1 - q.2 - x₁) a x₁| < ε := by
  have hcompact : IsCompact (Set.Icc s₀ s₁ ×ˢ Set.Icc a 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ∫ x₁ in Set.Ioo a p.2,
      x₁⁻¹ * upperRosserBoundaryMassAux (k + 1) (p.1 - p.2 - x₁) a x₁)
      (Set.Icc s₀ s₁ ×ˢ Set.Icc a 1) := by
    apply
      (continuousOn_integral_inv_mul_upperRosserBoundaryMassAux_outer_succ k ha).mono
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  have huniform := hcompact.uniformContinuousOn_of_continuous hcont
  simpa [Real.dist_eq] using
    (Metric.uniformContinuousOn_iff.mp huniform ε hε)

/-- Positive-depth residual-level continuity is uniform on every compact level
interval. -/
theorem uniformContinuousOn_upperRosserBoundaryMassAux_level_succ
    (k : ℕ) {a b r₀ r₁ : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    UniformContinuousOn
      (fun s => upperRosserBoundaryMassAux (k + 1) s a b) (Set.Icc r₀ r₁) :=
  isCompact_Icc.uniformContinuousOn_of_continuous
    (continuous_upperRosserBoundaryMassAux_level_succ k ha hb).continuousOn

/-- Quantitative residual-level modulus on a compact interval. -/
theorem exists_upperRosserBoundaryMassAux_level_modulus_succ
    (k : ℕ) {a b r₀ r₁ ε : ℝ} (ha : 0 < a) (hb : b ≤ 1) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Set.Icc r₀ r₁, ∀ t ∈ Set.Icc r₀ r₁, |s - t| < δ →
      |upperRosserBoundaryMassAux (k + 1) s a b -
        upperRosserBoundaryMassAux (k + 1) t a b| < ε := by
  have h := Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_upperRosserBoundaryMassAux_level_succ
      k (r₀ := r₀) (r₁ := r₁) ha hb) ε hε
  simpa [Real.dist_eq] using h

/-- On a sufficiently short residual-level cell, the left-endpoint value plus
an arbitrarily small error majorizes every positive-depth value in that cell. -/
theorem exists_upperRosserBoundaryMassAux_level_cell_majorant_succ
    (k : ℕ) {a b r₀ r₁ ε : ℝ} (ha : 0 < a) (hb : b ≤ 1) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {l r s : ℝ}, l ∈ Set.Icc r₀ r₁ → r ∈ Set.Icc r₀ r₁ →
      l ≤ s → s ≤ r → r - l < δ →
        upperRosserBoundaryMassAux (k + 1) s a b ≤
          upperRosserBoundaryMassAux (k + 1) l a b + ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    exists_upperRosserBoundaryMassAux_level_modulus_succ k ha hb hε
  refine ⟨δ, hδ, ?_⟩
  intro l r s hl hr hls hsr hlr
  have hs : s ∈ Set.Icc r₀ r₁ :=
    ⟨hl.1.trans hls, hsr.trans hr.2⟩
  have hdist : |s - l| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hls)]
    linarith
  have hclose := hmod s hs l hl hdist
  linarith [le_abs_self
    (upperRosserBoundaryMassAux (k + 1) s a b -
      upperRosserBoundaryMassAux (k + 1) l a b)]

/-- At fixed level and positive lower cutoff, enlarging an inherited upper face
up to the global cutoff can only increase the recursive boundary mass. -/
theorem upperRosserBoundaryMassAux_mono_upper
    (k : ℕ) {s a b d : ℝ} (ha : 0 < a) (hbd : b ≤ d) (hd : d ≤ 1) :
    upperRosserBoundaryMassAux k s a b ≤
      upperRosserBoundaryMassAux k s a d := by
  cases k with
  | zero =>
      rw [upperRosserBoundaryMassAux_zero, upperRosserBoundaryMassAux_zero]
  | succ k =>
      rw [upperRosserBoundaryMassAux_succ, upperRosserBoundaryMassAux_succ]
      apply MeasureTheory.setIntegral_mono_set
        (integrableOn_outer_integrand_upperRosserBoundaryMassAux k ha
          ((min_le_left d (s / 3)).trans hd))
      · filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
        apply mul_nonneg (inv_nonneg.mpr (ha.le.trans hx₀.1.le))
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
        exact mul_nonneg (inv_nonneg.mpr (ha.le.trans hx₁.1.le))
          (upperRosserBoundaryMassAux_nonneg k ha.le)
      · filter_upwards with x hx
        exact ⟨hx.1, hx.2.trans_le (min_le_min hbd le_rfl)⟩

/-- At fixed level and positive lower cutoff, every finite-depth boundary mass
is continuous in its inherited upper face on the global screened interval. -/
theorem continuousOn_upperRosserBoundaryMassAux_upper
    (k : ℕ) {s a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun b => upperRosserBoundaryMassAux k s a b)
      (Set.Icc a 1) := by
  cases k with
  | zero =>
      simp only [upperRosserBoundaryMassAux_zero]
      fun_prop
  | succ k =>
      by_cases hsa : s / 3 ≤ a
      · have hzero :
            (fun b => upperRosserBoundaryMassAux (k + 1) s a b) =
              fun _ => 0 := by
          funext b
          rw [upperRosserBoundaryMassAux_succ]
          have hempty : Set.Ioo a (min b (s / 3)) = ∅ :=
            Set.Ioo_eq_empty (by linarith [min_le_right b (s / 3)])
          rw [hempty, MeasureTheory.Measure.restrict_empty,
            MeasureTheory.integral_zero_measure]
        rw [hzero]
        exact continuousOn_const
      · have has : a ≤ s / 3 := le_of_not_ge hsa
        let f : ℝ → ℝ := fun x₀ => x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁
        have hfIoo : MeasureTheory.IntegrableOn f (Set.Ioo a 1) := by
          exact
            integrableOn_outer_integrand_upperRosserBoundaryMassAux k ha le_rfl
        have hfIcc : MeasureTheory.IntegrableOn f (Set.Icc a 1) :=
          (integrableOn_Icc_iff_integrableOn_Ioo).2 hfIoo
        have hprimitive :
            ContinuousOn (fun u => ∫ x in Set.Ioc a u, f x) (Set.Icc a 1) :=
          intervalIntegral.continuousOn_primitive hfIcc
        have hmin : ContinuousOn (fun b : ℝ => min b (s / 3))
            (Set.Icc a 1) :=
          (continuous_id.min continuous_const).continuousOn
        have hmaps : Set.MapsTo (fun b : ℝ => min b (s / 3))
            (Set.Icc a 1) (Set.Icc a 1) := by
          intro b hb
          exact ⟨le_min hb.1 has, (min_le_left _ _).trans hb.2⟩
        apply (hprimitive.comp hmin hmaps).congr
        intro b _
        change upperRosserBoundaryMassAux (k + 1) s a b =
          ∫ x₀ in Set.Ioc a (min b (s / 3)),
            x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
              x₁⁻¹ *
                upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁
        rw [upperRosserBoundaryMassAux_succ]
        exact (MeasureTheory.integral_Ioc_eq_integral_Ioo).symm

/-- On a positive screen, the cutoff dependence of every finite-depth boundary
mass has a modulus uniform across the whole inherited-cutoff interval. -/
theorem uniformContinuousOn_upperRosserBoundaryMassAux_upper
    (k : ℕ) {s a : ℝ} (ha : 0 < a) :
    UniformContinuousOn (fun b => upperRosserBoundaryMassAux k s a b)
      (Set.Icc a 1) :=
  isCompact_Icc.uniformContinuousOn_of_continuous
    (continuousOn_upperRosserBoundaryMassAux_upper k ha)

/-- Quantitative form of uniform cutoff continuity, suitable for controlling
right-endpoint majorants on a sufficiently fine finite partition. -/
theorem exists_upperRosserBoundaryMassAux_upper_modulus
    (k : ℕ) {s a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ > 0, ∀ b ∈ Set.Icc a 1, ∀ d ∈ Set.Icc a 1,
      |b - d| < δ →
        |upperRosserBoundaryMassAux k s a b -
          upperRosserBoundaryMassAux k s a d| < ε := by
  have h := (Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_upperRosserBoundaryMassAux_upper k (s := s) ha)) ε hε
  simpa [Real.dist_eq] using h

/-- On every sufficiently short cutoff cell, its right-endpoint boundary mass
majorizes all values in the cell and exceeds its left-endpoint value by less
than the prescribed error. -/
theorem exists_upperRosserBoundaryMassAux_cell_majorant
    (k : ℕ) {s a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {l r b : ℝ}, l ∈ Set.Icc a 1 → r ∈ Set.Icc a 1 →
      l ≤ b → b ≤ r → r - l < δ →
        upperRosserBoundaryMassAux k s a b ≤
          upperRosserBoundaryMassAux k s a l + ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    exists_upperRosserBoundaryMassAux_upper_modulus k (s := s) ha hε
  refine ⟨δ, hδ, ?_⟩
  intro l r b hl hr hlb hbr hlr
  have hwidth : |r - l| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hlb.trans hbr))]
    exact hlr
  have hclose := hmod r hr l hl hwidth
  have hright :
      upperRosserBoundaryMassAux k s a r <
        upperRosserBoundaryMassAux k s a l + ε := by
    linarith [le_abs_self
      (upperRosserBoundaryMassAux k s a r -
        upperRosserBoundaryMassAux k s a l)]
  exact (upperRosserBoundaryMassAux_mono_upper k ha hbr hr.2).trans hright.le

/-- A local rectangular-cell majorant combining residual-level continuity with
cutoff continuity.  The residual lower endpoint `l` and cutoff upper endpoint
`d` are fixed cell corners; taking the minimum of these finitely many local
moduli gives the mesh datum required by a finite two-stage Darboux partition. -/
theorem exists_upperRosserBoundaryMassAux_level_upper_cell_majorant_succ
    (k : ℕ) {a d r₀ r₁ l ε : ℝ}
    (ha : 0 < a) (hd : d ∈ Set.Icc a 1) (hl : l ∈ Set.Icc r₀ r₁)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ {s c b : ℝ}, s ∈ Set.Icc r₀ r₁ → c ∈ Set.Icc a 1 →
      l ≤ s → s - l < δ → c ≤ b → b ≤ d → d - c < δ →
        upperRosserBoundaryMassAux (k + 1) s a b ≤
          upperRosserBoundaryMassAux (k + 1) l a c + ε := by
  obtain ⟨δLevel, hδLevel, hlevel⟩ :=
    exists_upperRosserBoundaryMassAux_level_modulus_succ
      k ha hd.2 (half_pos hε)
  obtain ⟨δUpper, hδUpper, hupper⟩ :=
    exists_upperRosserBoundaryMassAux_cell_majorant
      (k + 1) (s := l) ha (half_pos hε)
  refine ⟨min δLevel δUpper, lt_min hδLevel hδUpper, ?_⟩
  intro s c b hs hc hls hsl hcb hbd hdc
  have hsLevel : |s - l| < δLevel := by
    rw [abs_of_nonneg (sub_nonneg.mpr hls)]
    exact hsl.trans_le (min_le_left _ _)
  have hlevel' := hlevel s hs l hl hsLevel
  have hlevelUpper :
      upperRosserBoundaryMassAux (k + 1) s a d <
        upperRosserBoundaryMassAux (k + 1) l a d + ε / 2 := by
    linarith [le_abs_self
      (upperRosserBoundaryMassAux (k + 1) s a d -
        upperRosserBoundaryMassAux (k + 1) l a d)]
  have hcutoff :
      upperRosserBoundaryMassAux (k + 1) l a d ≤
        upperRosserBoundaryMassAux (k + 1) l a c + ε / 2 :=
    hupper hc hd (hcb.trans hbd) le_rfl
      (hdc.trans_le (min_le_right _ _))
  exact le_of_lt <| calc
      upperRosserBoundaryMassAux (k + 1) s a b ≤
          upperRosserBoundaryMassAux (k + 1) s a d :=
        upperRosserBoundaryMassAux_mono_upper (k + 1) ha hbd hd.2
      _ < upperRosserBoundaryMassAux (k + 1) l a d + ε / 2 :=
        hlevelUpper
      _ ≤ upperRosserBoundaryMassAux (k + 1) l a c + ε := by
        linarith

/-- Specialization of the two-parameter cell estimate to the affine residual
`s - x₀ - x`.  On a short inner-coordinate cell, its lower residual corner and
lower cutoff jointly majorize every positive-depth residual, up to `ε`. -/
theorem exists_upperRosserBoundaryMassAux_inner_cell_majorant_succ
    (k : ℕ) {s x₀ a l r r₀ r₁ ε : ℝ}
    (ha : 0 < a) (hl : l ∈ Set.Icc a 1) (hr : r ∈ Set.Icc a 1)
    (hresL : s - x₀ - r ∈ Set.Icc r₀ r₁)
    (hresR : s - x₀ - l ∈ Set.Icc r₀ r₁) (hε : 0 < ε) :
    ∃ δ > 0, r - l < δ → ∀ x ∈ Set.Icc l r,
      upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x ≤
        upperRosserBoundaryMassAux (k + 1) (s - x₀ - r) a l + ε := by
  obtain ⟨δ, hδ, hcell⟩ :=
    exists_upperRosserBoundaryMassAux_level_upper_cell_majorant_succ
      k ha hr hresL hε
  refine ⟨δ, hδ, fun hlrδ x hx => ?_⟩
  apply hcell (s := s - x₀ - x) (c := l) (b := x)
  · constructor
    · exact hresL.1.trans (by linarith [hx.2])
    · exact (by linarith [hx.1] : s - x₀ - x ≤ s - x₀ - l).trans hresR.2
  · exact hl
  · linarith [hx.2]
  · linarith [hx.1, hlrδ]
  · exact hx.1
  · exact hx.2
  · exact hlrδ

/-- At positive residual depth, the residual level and inherited upper cutoff
vary jointly continuously on every compact screened rectangle.  Monotonicity in
the upper cutoff lets the two separate continuity estimates be combined without
requiring any regularity of the depth-zero integrand. -/
theorem continuousOn_upperRosserBoundaryMassAux_level_upper_succ
    (k : ℕ) {a r₀ r₁ : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun p : ℝ × ℝ => upperRosserBoundaryMassAux (k + 1) p.1 a p.2)
      (Set.Icc r₀ r₁ ×ˢ Set.Icc a 1) := by
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hεthird : 0 < ε / 3 := div_pos hε (by norm_num)
  have hcutAt :=
    (continuousOn_upperRosserBoundaryMassAux_upper
      (k + 1) (s := p.1) ha) p.2 hp.2
  rw [Metric.continuousWithinAt_iff] at hcutAt
  obtain ⟨δb, hδb, hcut⟩ := hcutAt (ε / 3) hεthird
  let blo : ℝ := max a (p.2 - δb / 2)
  let bhi : ℝ := min 1 (p.2 + δb / 2)
  have hpa : a ≤ p.2 := hp.2.1
  have hpone : p.2 ≤ 1 := hp.2.2
  have haone : a ≤ 1 := hpa.trans hpone
  have hblo : blo ∈ Set.Icc a 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le haone (by linarith [hpone, hδb])
  have hbhi : bhi ∈ Set.Icc a 1 := by
    constructor
    · exact le_min haone (by linarith [hpa, hδb])
    · exact min_le_left _ _
  have hblo_le : blo ≤ p.2 := by
    exact max_le hp.2.1 (by linarith)
  have hle_bhi : p.2 ≤ bhi := by
    exact le_min hp.2.2 (by linarith)
  have hdist_blo : dist blo p.2 < δb := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hblo_le)]
    have hlo := le_max_right a (p.2 - δb / 2)
    linarith
  have hdist_bhi : dist bhi p.2 < δb := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle_bhi)]
    have hhi := min_le_right (1 : ℝ) (p.2 + δb / 2)
    linarith
  have hcutLo := hcut hblo hdist_blo
  have hcutHi := hcut hbhi hdist_bhi
  have hlevelLo : ContinuousAt
      (fun t => upperRosserBoundaryMassAux (k + 1) t a blo) p.1 :=
    (continuous_upperRosserBoundaryMassAux_level_succ k ha hblo.2).continuousAt
  have hlevelHi : ContinuousAt
      (fun t => upperRosserBoundaryMassAux (k + 1) t a bhi) p.1 :=
    (continuous_upperRosserBoundaryMassAux_level_succ k ha hbhi.2).continuousAt
  rw [Metric.continuousAt_iff] at hlevelLo hlevelHi
  obtain ⟨δlo, hδlo, hresLo⟩ := hlevelLo (ε / 3) hεthird
  obtain ⟨δhi, hδhi, hresHi⟩ := hlevelHi (ε / 3) hεthird
  refine ⟨min (δb / 2) (min δlo δhi), by positivity, ?_⟩
  intro q hq hdist
  rw [Prod.dist_eq, max_lt_iff] at hdist
  have hqLevel : dist q.1 p.1 < δlo ∧ dist q.1 p.1 < δhi :=
    ⟨hdist.1.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hdist.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hqUpperDist : dist q.2 p.2 < δb / 2 :=
    hdist.2.trans_le (min_le_left _ _)
  have hqUpperAbs : |q.2 - p.2| < δb / 2 := by
    simpa [Real.dist_eq] using hqUpperDist
  have hbloq : blo ≤ q.2 := by
    apply max_le hq.2.1
    rw [abs_lt] at hqUpperAbs
    linarith
  have hqbhi : q.2 ≤ bhi := by
    apply le_min hq.2.2
    rw [abs_lt] at hqUpperAbs
    linarith
  have hmonoLo :
      upperRosserBoundaryMassAux (k + 1) q.1 a blo ≤
        upperRosserBoundaryMassAux (k + 1) q.1 a q.2 :=
    upperRosserBoundaryMassAux_mono_upper (k + 1) ha hbloq hq.2.2
  have hmonoHi :
      upperRosserBoundaryMassAux (k + 1) q.1 a q.2 ≤
        upperRosserBoundaryMassAux (k + 1) q.1 a bhi :=
    upperRosserBoundaryMassAux_mono_upper (k + 1) ha hqbhi hbhi.2
  have hresLo' := hresLo hqLevel.1
  have hresHi' := hresHi hqLevel.2
  rw [Real.dist_eq] at hcutLo hcutHi hresLo' hresHi' ⊢
  rw [abs_lt]
  constructor
  · have hcutLoOne :=
      le_abs_self
        (upperRosserBoundaryMassAux (k + 1) p.1 a p.2 -
          upperRosserBoundaryMassAux (k + 1) p.1 a blo)
    have hresLoOne :=
      le_abs_self
        (upperRosserBoundaryMassAux (k + 1) p.1 a blo -
          upperRosserBoundaryMassAux (k + 1) q.1 a blo)
    rw [abs_sub_comm] at hcutLo hresLo'
    linarith
  · have hresHiOne :=
      le_abs_self
        (upperRosserBoundaryMassAux (k + 1) q.1 a bhi -
          upperRosserBoundaryMassAux (k + 1) p.1 a bhi)
    have hcutHiOne :=
      le_abs_self
        (upperRosserBoundaryMassAux (k + 1) p.1 a bhi -
          upperRosserBoundaryMassAux (k + 1) p.1 a p.2)
    linarith

/-- Quantitative joint modulus for positive-depth residual mass on a compact
level/cutoff rectangle. -/
theorem exists_upperRosserBoundaryMassAux_level_upper_modulus_succ
    (k : ℕ) {a r₀ r₁ ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ Set.Icc r₀ r₁ ×ˢ Set.Icc a 1,
      ∀ q ∈ Set.Icc r₀ r₁ ×ˢ Set.Icc a 1, dist p q < δ →
        |upperRosserBoundaryMassAux (k + 1) p.1 a p.2 -
          upperRosserBoundaryMassAux (k + 1) q.1 a q.2| < ε := by
  have hcompact : IsCompact (Set.Icc r₀ r₁ ×ˢ Set.Icc a 1) :=
    isCompact_Icc.prod isCompact_Icc
  have huniform :=
    hcompact.uniformContinuousOn_of_continuous
      (continuousOn_upperRosserBoundaryMassAux_level_upper_succ k ha)
  simpa [Real.dist_eq] using
    (Metric.uniformContinuousOn_iff.mp huniform ε hε)

/-- At fixed residual level and positive lower cutoff, the inherited upper face
varies continuously on any compact interval below the global cutoff, including
the part where that face lies below the lower cutoff and the mass vanishes. -/
theorem continuousOn_upperRosserBoundaryMassAux_upper_global
    (k : ℕ) {s a c : ℝ} (ha : 0 < a) :
    ContinuousOn (fun b => upperRosserBoundaryMassAux k s a b) (Set.Icc c 1) := by
  cases k with
  | zero =>
      simp only [upperRosserBoundaryMassAux_zero]
      fun_prop
  | succ k =>
      by_cases ha1 : a ≤ 1
      · let f : ℝ → ℝ := fun x₀ => x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁
        have hfIoo : MeasureTheory.IntegrableOn f (Set.Ioo a 1) :=
          integrableOn_outer_integrand_upperRosserBoundaryMassAux k ha le_rfl
        have hfIcc : MeasureTheory.IntegrableOn f (Set.Icc a 1) :=
          (integrableOn_Icc_iff_integrableOn_Ioo).2 hfIoo
        have hprimitive :
            ContinuousOn (fun u => ∫ x in Set.Ioc a u, f x) (Set.Icc a 1) :=
          intervalIntegral.continuousOn_primitive hfIcc
        let endpoint : ℝ → ℝ := fun b => max a (min b (s / 3))
        have hendpoint : ContinuousOn endpoint (Set.Icc c 1) :=
          (continuous_const.max (continuous_id.min continuous_const)).continuousOn
        have hmaps : Set.MapsTo endpoint (Set.Icc c 1) (Set.Icc a 1) := by
          intro b hb
          exact ⟨le_max_left _ _,
            max_le ha1 ((min_le_left b (s / 3)).trans hb.2)⟩
        apply (hprimitive.comp hendpoint hmaps).congr
        intro b hb
        change upperRosserBoundaryMassAux (k + 1) s a b =
          ∫ x₀ in Set.Ioc a (endpoint b), f x₀
        rw [upperRosserBoundaryMassAux_succ,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
        by_cases h : a < min b (s / 3)
        · rw [show endpoint b = min b (s / 3) by
            simp [endpoint, max_eq_right h.le]]
        · have hle : min b (s / 3) ≤ a := le_of_not_gt h
          rw [show endpoint b = a by simp [endpoint, max_eq_left hle],
            Set.Ioo_eq_empty (not_lt.mpr hle), Set.Ioo_self,
            MeasureTheory.Measure.restrict_empty,
            MeasureTheory.integral_zero_measure]
      · refine ContinuousOn.congr (f := fun _ : ℝ => 0) continuousOn_const ?_
        intro b hb
        change upperRosserBoundaryMassAux (k + 1) s a b = 0
        rw [upperRosserBoundaryMassAux_succ]
        have hle : min b (s / 3) ≤ a :=
          (min_le_left b (s / 3)).trans (hb.2.trans (le_of_not_ge ha1))
        rw [Set.Ioo_eq_empty (not_lt.mpr hle),
          MeasureTheory.Measure.restrict_empty,
          MeasureTheory.integral_zero_measure]

/-- Positive-depth residual mass has one uniform modulus in the residual level,
lower cutoff, and inherited upper face on every screened compact box. -/
theorem exists_upperRosserBoundaryMassAux_level_lower_upper_modulus_succ
    (k : ℕ) {r₀ r₁ c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0,
      ∀ p ∈ (Set.Icc r₀ r₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1,
      ∀ q ∈ (Set.Icc r₀ r₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1,
        dist p q < δ →
          |upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 p.2 -
            upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 q.2| < ε := by
  let C := (Set.Icc r₀ r₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1
  have hcontinuous : ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ =>
        upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 p.2) C := by
    intro p hp
    rw [Metric.continuousWithinAt_iff]
    intro η hη
    have hηthird : 0 < η / 3 := div_pos hη (by norm_num)
    have hcutAt :=
      (continuousOn_upperRosserBoundaryMassAux_upper_global
        (k + 1) (s := p.1.1) (a := p.1.2)
        (c := c) (hc.trans_le hp.1.2.1)) p.2 hp.2
    rw [Metric.continuousWithinAt_iff] at hcutAt
    obtain ⟨δb, hδb, hcut⟩ := hcutAt (η / 3) hηthird
    let blo : ℝ := max c (p.2 - δb / 2)
    let bhi : ℝ := min 1 (p.2 + δb / 2)
    have hblo : blo ∈ Set.Icc c 1 := by
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith [hp.2.1, hp.2.2])
          (by linarith [hp.2.2, hδb])
    have hbhi : bhi ∈ Set.Icc c 1 := by
      constructor
      · exact le_min (by linarith [hp.2.1, hp.2.2])
          (by linarith [hp.2.1, hδb])
      · exact min_le_left _ _
    have hblo_le : blo ≤ p.2 :=
      max_le hp.2.1 (by linarith)
    have hle_bhi : p.2 ≤ bhi :=
      le_min hp.2.2 (by linarith)
    have hdist_blo : dist blo p.2 < δb := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hblo_le)]
      have hlo := le_max_right c (p.2 - δb / 2)
      linarith
    have hdist_bhi : dist bhi p.2 < δb := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle_bhi)]
      have hhi := min_le_right (1 : ℝ) (p.2 + δb / 2)
      linarith
    have hcutLo := hcut hblo hdist_blo
    have hcutHi := hcut hbhi hdist_bhi
    have hlowerLo : ContinuousAt
        (fun q : ℝ × ℝ =>
          upperRosserBoundaryMassAux (k + 1) q.1 q.2 blo) p.1 :=
      continuousAt_upperRosserBoundaryMassAux_level_lower_succ
        k (hc.trans_le hp.1.2.1) hblo.2
    have hlowerHi : ContinuousAt
        (fun q : ℝ × ℝ =>
          upperRosserBoundaryMassAux (k + 1) q.1 q.2 bhi) p.1 :=
      continuousAt_upperRosserBoundaryMassAux_level_lower_succ
        k (hc.trans_le hp.1.2.1) hbhi.2
    rw [Metric.continuousAt_iff] at hlowerLo hlowerHi
    obtain ⟨δlo, hδlo, hresLo⟩ := hlowerLo (η / 3) hηthird
    obtain ⟨δhi, hδhi, hresHi⟩ := hlowerHi (η / 3) hηthird
    refine ⟨min (δb / 2) (min δlo δhi), by positivity, ?_⟩
    intro q hq hdist
    rw [Prod.dist_eq, max_lt_iff] at hdist
    have hqParams : dist q.1 p.1 < δlo ∧ dist q.1 p.1 < δhi :=
      ⟨hdist.1.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
        hdist.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hqUpperDist : dist q.2 p.2 < δb / 2 :=
      hdist.2.trans_le (min_le_left _ _)
    have hqUpperAbs : |q.2 - p.2| < δb / 2 := by
      simpa [Real.dist_eq] using hqUpperDist
    have hbloq : blo ≤ q.2 := by
      apply max_le hq.2.1
      rw [abs_lt] at hqUpperAbs
      linarith
    have hqbhi : q.2 ≤ bhi := by
      apply le_min hq.2.2
      rw [abs_lt] at hqUpperAbs
      linarith
    have hmonoLo :
        upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 blo ≤
          upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 q.2 :=
      upperRosserBoundaryMassAux_mono_upper
        (k + 1) (hc.trans_le hq.1.2.1) hbloq hq.2.2
    have hmonoHi :
        upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 q.2 ≤
          upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 bhi :=
      upperRosserBoundaryMassAux_mono_upper
        (k + 1) (hc.trans_le hq.1.2.1) hqbhi hbhi.2
    have hresLo' := hresLo hqParams.1
    have hresHi' := hresHi hqParams.2
    rw [Real.dist_eq] at hcutLo hcutHi hresLo' hresHi' ⊢
    rw [abs_lt]
    constructor
    · have hcutLoOne := le_abs_self
          (upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 p.2 -
            upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 blo)
      have hresLoOne := le_abs_self
          (upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 blo -
            upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 blo)
      rw [abs_sub_comm] at hcutLo hresLo'
      linarith
    · have hresHiOne := le_abs_self
          (upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 bhi -
            upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 bhi)
      have hcutHiOne := le_abs_self
          (upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 bhi -
            upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 p.2)
      linarith
  have hcompact : IsCompact C :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have huniform := hcompact.uniformContinuousOn_of_continuous hcontinuous
  simpa [C, Real.dist_eq] using
    (Metric.uniformContinuousOn_iff.mp huniform ε hε)

/-- Moving the positive lower cutoff of a positive-depth inner Rosser integral
through a sufficiently short interval changes the integral by an arbitrarily
small amount, uniformly in the residual level and outer coordinate on a compact
screened box. -/
theorem exists_integral_inv_mul_upperRosserBoundaryMassAux_lower_modulus_succ
    (k : ℕ) {s₀ s₁ c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {s x₀ l a : ℝ},
      s ∈ Set.Icc s₀ s₁ → x₀ ∈ Set.Icc c 1 →
      l ∈ Set.Icc c 1 → a ∈ Set.Icc c 1 →
      l ≤ a → a - l < δ →
      (∫ x in Set.Ioo l x₀, x⁻¹ *
          upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) l x) ≤
        (∫ x in Set.Ioo a x₀, x⁻¹ *
          upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x) + ε := by
  let B : ℝ := c⁻¹ * (c⁻¹ * c⁻¹) ^ (k + 1)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain ⟨δMass, hδMass, hmod⟩ :=
    exists_upperRosserBoundaryMassAux_level_lower_upper_modulus_succ
      k (r₀ := s₀ - 2) (r₁ := s₁ - 2 * c) (c := c)
        (ε := ε * c / 4) hc (by positivity)
  let δ := min δMass (ε / (4 * B))
  have hδ : 0 < δ := lt_min hδMass (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s x₀ l a hs hx₀ hl ha hla hwidth
  let gL : ℝ → ℝ := fun x => x⁻¹ *
    upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) l x
  let gA : ℝ → ℝ := fun x => x⁻¹ *
    upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x
  have hintL : MeasureTheory.IntegrableOn gL (Set.Ioo l x₀) := by
    simpa [gL] using
      integrableOn_inv_mul_upperRosserBoundaryMassAux
        (k + 1) (s := s - x₀) (a := l) (b := x₀)
          (hc.trans_le hl.1) hx₀.2
  have hintA : MeasureTheory.IntegrableOn gA (Set.Ioo a x₀) := by
    simpa [gA] using
      integrableOn_inv_mul_upperRosserBoundaryMassAux
        (k + 1) (s := s - x₀) (a := a) (b := x₀)
          (hc.trans_le ha.1) hx₀.2
  have hgLBound : ∀ x ∈ Set.Ioo l x₀, 0 ≤ gL x ∧ gL x ≤ B := by
    intro x hx
    have hxpos : 0 < x := hc.trans_le hl.1 |>.trans hx.1
    have hxinv : x⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hxpos hc).2 (hl.1.trans hx.1.le)
    have hmassNonneg :
        0 ≤ upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) l x :=
      upperRosserBoundaryMassAux_nonneg (k + 1) (hc.le.trans hl.1)
    have hmass :
        upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) l x ≤
          (c⁻¹ * c⁻¹) ^ (k + 1) :=
      upperRosserBoundaryMassAux_le_of_lower_bound
        (k + 1) hc hl.1 (hx.2.le.trans hx₀.2)
    exact ⟨mul_nonneg (inv_nonneg.mpr hxpos.le) hmassNonneg,
      by
        dsimp [gL, B]
        exact mul_le_mul hxinv hmass hmassNonneg (inv_nonneg.mpr hc.le)⟩
  have hshort : ∀ {u : ℝ}, l ≤ u → u ≤ a → u ≤ x₀ →
      (∫ x in Set.Ioo l u, gL x) ≤ ε / 4 := by
    intro u hlu hua hux₀
    have hintLU : MeasureTheory.IntegrableOn gL (Set.Ioo l u) :=
      hintL.mono_set fun x hx => ⟨hx.1, hx.2.trans_le hux₀⟩
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ => B) (Set.Ioo l u) :=
      MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    calc
      (∫ x in Set.Ioo l u, gL x) ≤ ∫ _x in Set.Ioo l u, B := by
        apply MeasureTheory.setIntegral_mono_on hintLU hconst measurableSet_Ioo
        intro x hx
        exact (hgLBound x ⟨hx.1, hx.2.trans_le hux₀⟩).2
      _ = (u - l) * B := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hlu)]
        rfl
      _ ≤ ε / 4 := by
        have hbudget : a - l < ε / (4 * B) :=
          hwidth.trans_le (min_le_right _ _)
        have hubudget : u - l < ε / (4 * B) := by linarith
        have := mul_lt_mul_of_pos_right hubudget hB
        have hcancel : ε / (4 * B) * B = ε / 4 := by
          field_simp [hB.ne']
        rw [hcancel] at this
        linarith
  by_cases hax₀ : a ≤ x₀
  · have hintLCommon : MeasureTheory.IntegrableOn gL (Set.Ioo a x₀) :=
      hintL.mono_set fun x hx => ⟨hla.trans_lt hx.1, hx.2⟩
    have hcommonPoint : ∀ x ∈ Set.Ioo a x₀, gL x ≤ gA x + ε / 4 := by
      intro x hx
      have hxmem : x ∈ Set.Icc c 1 :=
        ⟨ha.1.trans hx.1.le, hx.2.le.trans hx₀.2⟩
      have hres : s - x₀ - x ∈ Set.Icc (s₀ - 2) (s₁ - 2 * c) := by
        constructor
        · linarith [hs.1, hx₀.2, hxmem.2]
        · linarith [hs.2, hx₀.1, hxmem.1]
      have hp :
          ((s - x₀ - x, l), x) ∈
            (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ
              Set.Icc c 1 :=
        ⟨⟨hres, hl⟩, hxmem⟩
      have hq :
          ((s - x₀ - x, a), x) ∈
            (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ
              Set.Icc c 1 :=
        ⟨⟨hres, ha⟩, hxmem⟩
      have hdist :
          dist ((s - x₀ - x, l), x) ((s - x₀ - x, a), x) < δMass := by
        calc
          dist ((s - x₀ - x, l), x) ((s - x₀ - x, a), x) =
              max (max (dist (s - x₀ - x) (s - x₀ - x)) (dist l a))
                (dist x x) := by rw [Prod.dist_eq, Prod.dist_eq]
          _ = a - l := by
            simp [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hla),
              sub_nonneg.mpr hla]
          _ < δMass := hwidth.trans_le (min_le_left _ _)
      have hclose := hmod _ hp _ hq hdist
      have hmassLe :=
        le_abs_self
          (upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) l x -
            upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x)
      have hmass :
          upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) l x ≤
            upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x +
              ε * c / 4 := by
        linarith
      have hxinv : x⁻¹ ≤ c⁻¹ :=
        (inv_le_inv₀ (hc.trans_le hxmem.1) hc).2 hxmem.1
      have hmassA :
          0 ≤ upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x :=
        upperRosserBoundaryMassAux_nonneg (k + 1) (hc.le.trans ha.1)
      calc
        gL x ≤ x⁻¹ *
            (upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x +
              ε * c / 4) :=
          mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr (hc.le.trans hxmem.1))
        _ = gA x + x⁻¹ * (ε * c / 4) := by
          dsimp [gL, gA]
          ring
        _ ≤ gA x + c⁻¹ * (ε * c / 4) := by
          gcongr
        _ = gA x + ε / 4 := by
          field_simp [hc.ne']
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ => ε / 4) (Set.Ioo a x₀) :=
      MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    have hcommon :
        (∫ x in Set.Ioo a x₀, gL x) ≤
          (∫ x in Set.Ioo a x₀, gA x) + ε / 4 := by
      calc
        (∫ x in Set.Ioo a x₀, gL x) ≤
            ∫ x in Set.Ioo a x₀, (gA x + ε / 4) := by
          apply MeasureTheory.setIntegral_mono_on
            hintLCommon (hintA.add hconst) measurableSet_Ioo
          exact hcommonPoint
        _ = (∫ x in Set.Ioo a x₀, gA x) +
            (x₀ - a) * (ε / 4) := by
          rw [MeasureTheory.integral_add hintA hconst,
            MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
            Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hax₀)]
          rfl
        _ ≤ (∫ x in Set.Ioo a x₀, gA x) + ε / 4 := by
          have hlength : x₀ - a ≤ 1 := by linarith [hx₀.2, ha.1]
          gcongr
          exact mul_le_of_le_one_left (div_nonneg hε.le (by norm_num)) hlength
    have hintLA : MeasureTheory.IntegrableOn gL (Set.Ioo l a) :=
      hintL.mono_set fun x hx => ⟨hx.1, hx.2.trans_le hax₀⟩
    have hdecomp :
        (∫ x in Set.Ioo l x₀, gL x) =
          (∫ x in Set.Ioo l a, gL x) + ∫ x in Set.Ioo a x₀, gL x := by
      calc
        (∫ x in Set.Ioo l x₀, gL x) = ∫ x in l..x₀, gL x := by
          rw [intervalIntegral.integral_of_le (hla.trans hax₀),
            MeasureTheory.integral_Ioc_eq_integral_Ioo]
        _ = (∫ x in l..a, gL x) + ∫ x in a..x₀, gL x :=
          (intervalIntegral.integral_add_adjacent_intervals
            ((intervalIntegrable_iff_integrableOn_Ioo_of_le hla).2 hintLA)
            ((intervalIntegrable_iff_integrableOn_Ioo_of_le hax₀).2
              hintLCommon)).symm
        _ = (∫ x in Set.Ioo l a, gL x) +
            ∫ x in Set.Ioo a x₀, gL x := by
          rw [intervalIntegral.integral_of_le hla,
            intervalIntegral.integral_of_le hax₀]
          simp_rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    change (∫ x in Set.Ioo l x₀, gL x) ≤
      (∫ x in Set.Ioo a x₀, gA x) + ε
    rw [hdecomp]
    linarith [hshort hla le_rfl hax₀]
  · have hx₀a : x₀ ≤ a := le_of_not_ge hax₀
    have hempty : Set.Ioo a x₀ = ∅ := Set.Ioo_eq_empty (not_lt.mpr hx₀a)
    change (∫ x in Set.Ioo l x₀, gL x) ≤
      (∫ x in Set.Ioo a x₀, gA x) + ε
    rw [hempty, MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure, zero_add]
    by_cases hlx₀ : l ≤ x₀
    · exact (hshort hlx₀ hx₀a le_rfl).trans (by linarith)
    · rw [Set.Ioo_eq_empty (not_lt.mpr (le_of_not_ge hlx₀)),
        MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure]
      exact hε.le

/-- Increasing the outer endpoint of a positive-depth inner Rosser integral by
a short amount has uniformly small cost, simultaneously for every lower cutoff
in a compact positive screen. -/
theorem exists_integral_inv_mul_upperRosserBoundaryMassAux_outer_endpoint_modulus_succ
    (k : ℕ) {s₀ s₁ c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {s a x₀ y₀ : ℝ},
      s ∈ Set.Icc s₀ s₁ → a ∈ Set.Icc c 1 →
      x₀ ∈ Set.Icc c 1 → y₀ ∈ Set.Icc c 1 →
      a ≤ x₀ → x₀ ≤ y₀ → y₀ - x₀ < δ →
      (∫ x in Set.Ioo a y₀, x⁻¹ *
          upperRosserBoundaryMassAux (k + 1) (s - y₀ - x) a x) ≤
        (∫ x in Set.Ioo a x₀, x⁻¹ *
          upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x) + ε := by
  let B : ℝ := c⁻¹ * (c⁻¹ * c⁻¹) ^ (k + 1)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain ⟨δMass, hδMass, hmod⟩ :=
    exists_upperRosserBoundaryMassAux_level_lower_upper_modulus_succ
      k (r₀ := s₀ - 2) (r₁ := s₁ - 2 * c) (c := c)
        (ε := ε * c / 4) hc (by positivity)
  let δ := min δMass (ε / (4 * B))
  have hδ : 0 < δ := lt_min hδMass (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s a x₀ y₀ hs ha hx₀ hy₀ hax hxy hwidth
  let gX : ℝ → ℝ := fun x => x⁻¹ *
    upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x
  let gY : ℝ → ℝ := fun x => x⁻¹ *
    upperRosserBoundaryMassAux (k + 1) (s - y₀ - x) a x
  have hintX : MeasureTheory.IntegrableOn gX (Set.Ioo a x₀) := by
    simpa [gX] using
      integrableOn_inv_mul_upperRosserBoundaryMassAux
        (k + 1) (s := s - x₀) (a := a) (b := x₀)
          (hc.trans_le ha.1) hx₀.2
  have hintY : MeasureTheory.IntegrableOn gY (Set.Ioo a y₀) := by
    simpa [gY] using
      integrableOn_inv_mul_upperRosserBoundaryMassAux
        (k + 1) (s := s - y₀) (a := a) (b := y₀)
          (hc.trans_le ha.1) hy₀.2
  have hgYBound : ∀ t ∈ Set.Ioo a y₀, 0 ≤ gY t ∧ gY t ≤ B := by
    intro t ht
    have htpos : 0 < t := hc.trans_le ha.1 |>.trans ht.1
    have htinv : t⁻¹ ≤ c⁻¹ :=
      (inv_le_inv₀ htpos hc).2 (ha.1.trans ht.1.le)
    have hmassNonneg :
        0 ≤ upperRosserBoundaryMassAux (k + 1) (s - y₀ - t) a t :=
      upperRosserBoundaryMassAux_nonneg (k + 1) (hc.le.trans ha.1)
    have hmass :
        upperRosserBoundaryMassAux (k + 1) (s - y₀ - t) a t ≤
          (c⁻¹ * c⁻¹) ^ (k + 1) :=
      upperRosserBoundaryMassAux_le_of_lower_bound
        (k + 1) hc ha.1 (ht.2.le.trans hy₀.2)
    exact ⟨mul_nonneg (inv_nonneg.mpr htpos.le) hmassNonneg,
      by
        dsimp [gY, B]
        exact mul_le_mul htinv hmass hmassNonneg (inv_nonneg.mpr hc.le)⟩
  have hcommonPoint : ∀ t ∈ Set.Ioo a x₀, gY t ≤ gX t + ε / 4 := by
    intro t ht
    have htmem : t ∈ Set.Icc c 1 :=
      ⟨ha.1.trans ht.1.le, ht.2.le.trans hx₀.2⟩
    have hresY : s - y₀ - t ∈ Set.Icc (s₀ - 2) (s₁ - 2 * c) := by
      constructor
      · linarith [hs.1, hy₀.2, htmem.2]
      · linarith [hs.2, hy₀.1, htmem.1]
    have hresX : s - x₀ - t ∈ Set.Icc (s₀ - 2) (s₁ - 2 * c) := by
      constructor
      · linarith [hs.1, hx₀.2, htmem.2]
      · linarith [hs.2, hx₀.1, htmem.1]
    have hp :
        ((s - y₀ - t, a), t) ∈
          (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ
            Set.Icc c 1 :=
      ⟨⟨hresY, ha⟩, htmem⟩
    have hq :
        ((s - x₀ - t, a), t) ∈
          (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ
            Set.Icc c 1 :=
      ⟨⟨hresX, ha⟩, htmem⟩
    have hdist :
        dist ((s - y₀ - t, a), t) ((s - x₀ - t, a), t) < δMass := by
      calc
        dist ((s - y₀ - t, a), t) ((s - x₀ - t, a), t) =
            y₀ - x₀ := by
          rw [Prod.dist_eq, Prod.dist_eq]
          simp only [dist_self, Real.dist_eq]
          rw [show |s - y₀ - t - (s - x₀ - t)| = y₀ - x₀ by
            rw [abs_of_nonpos (by linarith)]
            ring]
          simp [sub_nonneg.mpr hxy]
        _ < δMass := hwidth.trans_le (min_le_left _ _)
    have hclose := hmod _ hp _ hq hdist
    have hmassLe := le_abs_self
      (upperRosserBoundaryMassAux (k + 1) (s - y₀ - t) a t -
        upperRosserBoundaryMassAux (k + 1) (s - x₀ - t) a t)
    have hmass :
        upperRosserBoundaryMassAux (k + 1) (s - y₀ - t) a t ≤
          upperRosserBoundaryMassAux (k + 1) (s - x₀ - t) a t +
            ε * c / 4 := by
      linarith
    have htinv : t⁻¹ ≤ c⁻¹ :=
      (inv_le_inv₀ (hc.trans_le htmem.1) hc).2 htmem.1
    calc
      gY t ≤ t⁻¹ *
          (upperRosserBoundaryMassAux (k + 1) (s - x₀ - t) a t +
            ε * c / 4) :=
        mul_le_mul_of_nonneg_left hmass
          (inv_nonneg.mpr (hc.le.trans htmem.1))
      _ = gX t + t⁻¹ * (ε * c / 4) := by
        dsimp [gX, gY]
        ring
      _ ≤ gX t + c⁻¹ * (ε * c / 4) := by
        gcongr
      _ = gX t + ε / 4 := by
        field_simp [hc.ne']
  have hintYCommon : MeasureTheory.IntegrableOn gY (Set.Ioo a x₀) :=
    hintY.mono_set fun t ht => ⟨ht.1, ht.2.trans_le hxy⟩
  have hconstQuarter :
      MeasureTheory.IntegrableOn (fun _ : ℝ => ε / 4) (Set.Ioo a x₀) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  have hcommon :
      (∫ t in Set.Ioo a x₀, gY t) ≤
        (∫ t in Set.Ioo a x₀, gX t) + ε / 4 := by
    calc
      (∫ t in Set.Ioo a x₀, gY t) ≤
          ∫ t in Set.Ioo a x₀, (gX t + ε / 4) := by
        apply MeasureTheory.setIntegral_mono_on
          hintYCommon (hintX.add hconstQuarter) measurableSet_Ioo
        exact hcommonPoint
      _ = (∫ t in Set.Ioo a x₀, gX t) +
          (x₀ - a) * (ε / 4) := by
        rw [MeasureTheory.integral_add hintX hconstQuarter,
          MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hax)]
        rfl
      _ ≤ (∫ t in Set.Ioo a x₀, gX t) + ε / 4 := by
        have hlength : x₀ - a ≤ 1 := by linarith [hx₀.2, ha.1]
        gcongr
        exact mul_le_of_le_one_left (div_nonneg hε.le (by norm_num)) hlength
  have hintYShort : MeasureTheory.IntegrableOn gY (Set.Ioo x₀ y₀) :=
    hintY.mono_set fun t ht => ⟨hax.trans_lt ht.1, ht.2⟩
  have hconstB :
      MeasureTheory.IntegrableOn (fun _ : ℝ => B) (Set.Ioo x₀ y₀) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  have hshort : (∫ t in Set.Ioo x₀ y₀, gY t) ≤ ε / 4 := by
    calc
      (∫ t in Set.Ioo x₀ y₀, gY t) ≤ ∫ _t in Set.Ioo x₀ y₀, B := by
        apply MeasureTheory.setIntegral_mono_on
          hintYShort hconstB measurableSet_Ioo
        intro t ht
        exact (hgYBound t ⟨hax.trans_lt ht.1, ht.2⟩).2
      _ = (y₀ - x₀) * B := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)]
        rfl
      _ ≤ ε / 4 := by
        have hbudget : y₀ - x₀ < ε / (4 * B) :=
          hwidth.trans_le (min_le_right _ _)
        have hmul := mul_lt_mul_of_pos_right hbudget hB
        have hcancel : ε / (4 * B) * B = ε / 4 := by
          field_simp [hB.ne']
        rw [hcancel] at hmul
        exact hmul.le
  have hdecomp :
      (∫ t in Set.Ioo a y₀, gY t) =
        (∫ t in Set.Ioo a x₀, gY t) + ∫ t in Set.Ioo x₀ y₀, gY t := by
    calc
      (∫ t in Set.Ioo a y₀, gY t) = ∫ t in a..y₀, gY t := by
        rw [intervalIntegral.integral_of_le (hax.trans hxy),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = (∫ t in a..x₀, gY t) + ∫ t in x₀..y₀, gY t :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hax).2 hintYCommon)
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hxy).2
            hintYShort)).symm
      _ = (∫ t in Set.Ioo a x₀, gY t) +
          ∫ t in Set.Ioo x₀ y₀, gY t := by
        rw [intervalIntegral.integral_of_le hax,
          intervalIntegral.integral_of_le hxy]
        simp_rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  dsimp [gY, gX] at hdecomp hcommon hshort ⊢
  rw [hdecomp]
  linarith

/-- The outer-endpoint modulus also covers the unique mesh cell crossing the
moving lower cutoff: below the cutoff the integral vanishes, while the
remaining strip has uniformly bounded length. -/
theorem
    exists_integral_inv_mul_upperRosserBoundaryMassAux_outer_endpoint_modulus_succ_global
    (k : ℕ) {s₀ s₁ c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {s a x₀ y₀ : ℝ},
      s ∈ Set.Icc s₀ s₁ → a ∈ Set.Icc c 1 →
      x₀ ∈ Set.Icc c 1 → y₀ ∈ Set.Icc c 1 →
      x₀ ≤ y₀ → y₀ - x₀ < δ →
      (∫ x in Set.Ioo a y₀, x⁻¹ *
          upperRosserBoundaryMassAux (k + 1) (s - y₀ - x) a x) ≤
        (∫ x in Set.Ioo a x₀, x⁻¹ *
          upperRosserBoundaryMassAux (k + 1) (s - x₀ - x) a x) + ε := by
  let B : ℝ := c⁻¹ * (c⁻¹ * c⁻¹) ^ (k + 1)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain ⟨δEndpoint, hδEndpoint, hendpoint⟩ :=
    exists_integral_inv_mul_upperRosserBoundaryMassAux_outer_endpoint_modulus_succ
      k (s₀ := s₀) (s₁ := s₁) hc hε
  let δ := min δEndpoint (ε / B)
  have hδ : 0 < δ := lt_min hδEndpoint (div_pos hε hB)
  refine ⟨δ, hδ, ?_⟩
  intro s a x₀ y₀ hs ha hx₀ hy₀ hxy hwidth
  by_cases hax : a ≤ x₀
  · exact hendpoint hs ha hx₀ hy₀ hax hxy
      (hwidth.trans_le (min_le_left _ _))
  · have hxa : x₀ < a := lt_of_not_ge hax
    have hemptyX : Set.Ioo a x₀ = ∅ := Set.Ioo_eq_empty (not_lt.mpr hxa.le)
    by_cases hay : a < y₀
    · let gY : ℝ → ℝ := fun x => x⁻¹ *
        upperRosserBoundaryMassAux (k + 1) (s - y₀ - x) a x
      have hintY : MeasureTheory.IntegrableOn gY (Set.Ioo a y₀) := by
        simpa [gY] using
          integrableOn_inv_mul_upperRosserBoundaryMassAux
            (k + 1) (s := s - y₀) (a := a) (b := y₀)
              (hc.trans_le ha.1) hy₀.2
      have hbound : ∀ t ∈ Set.Ioo a y₀, gY t ≤ B := by
        intro t ht
        have htpos : 0 < t := hc.trans_le ha.1 |>.trans ht.1
        have htinv : t⁻¹ ≤ c⁻¹ :=
          (inv_le_inv₀ htpos hc).2 (ha.1.trans ht.1.le)
        have hmassNonneg :
            0 ≤ upperRosserBoundaryMassAux (k + 1) (s - y₀ - t) a t :=
          upperRosserBoundaryMassAux_nonneg (k + 1) (hc.le.trans ha.1)
        have hmass :
            upperRosserBoundaryMassAux (k + 1) (s - y₀ - t) a t ≤
              (c⁻¹ * c⁻¹) ^ (k + 1) :=
          upperRosserBoundaryMassAux_le_of_lower_bound
            (k + 1) hc ha.1 (ht.2.le.trans hy₀.2)
        dsimp [gY, B]
        exact mul_le_mul htinv hmass hmassNonneg (inv_nonneg.mpr hc.le)
      have hconst :
          MeasureTheory.IntegrableOn (fun _ : ℝ => B) (Set.Ioo a y₀) :=
        MeasureTheory.integrableOn_const (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
      have hintegral : (∫ t in Set.Ioo a y₀, gY t) ≤ B * (y₀ - a) := by
        calc
          (∫ t in Set.Ioo a y₀, gY t) ≤ ∫ _t in Set.Ioo a y₀, B := by
            apply MeasureTheory.setIntegral_mono_on
              hintY hconst measurableSet_Ioo
            exact hbound
          _ = (y₀ - a) * B := by
            rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
              Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hay.le)]
            rfl
          _ = B * (y₀ - a) := by ring
      have hlength : y₀ - a ≤ y₀ - x₀ := by linarith
      have hbudget : y₀ - x₀ < ε / B :=
        hwidth.trans_le (min_le_right _ _)
      have hstrip : B * (y₀ - a) < ε := by
        calc
          B * (y₀ - a) ≤ B * (y₀ - x₀) :=
            mul_le_mul_of_nonneg_left hlength hB.le
          _ < B * (ε / B) := mul_lt_mul_of_pos_left hbudget hB
          _ = ε := by field_simp [hB.ne']
      rw [hemptyX, MeasureTheory.Measure.restrict_empty,
        MeasureTheory.integral_zero_measure, zero_add]
      exact (by simpa [gY] using (hintegral.trans_lt hstrip).le)
    · have hya : y₀ ≤ a := le_of_not_gt hay
      have hemptyY : Set.Ioo a y₀ = ∅ := Set.Ioo_eq_empty (not_lt.mpr hya)
      simp only [hemptyX, hemptyY, MeasureTheory.Measure.restrict_empty,
        MeasureTheory.integral_zero_measure]
      simpa using hε.le


end MathlibNt.SieveTheory.LinearSieve
