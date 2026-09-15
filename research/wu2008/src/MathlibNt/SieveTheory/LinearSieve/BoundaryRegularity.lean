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

/-- Uniform norm bound for the inner integral, shared by integrability and
dominated-convergence arguments. -/
private theorem norm_integral_inv_mul_upperRosserBoundaryMassAux_le
    (k : ℕ) {s a x₀ : ℝ} (ha : 0 < a) (hx₀ : x₀ ≤ 1) :
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
    _ ≤ a⁻¹ * (a⁻¹ * a⁻¹) ^ k :=
      mul_le_of_le_one_right
        (mul_nonneg (inv_nonneg.mpr ha.le)
          (pow_nonneg (mul_nonneg (inv_nonneg.mpr ha.le)
            (inv_nonneg.mpr ha.le)) k)) (volume_Ioo_real_le_one ha hx₀)

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
  have hinnerNorm :=
    norm_integral_inv_mul_upperRosserBoundaryMassAux_le k (s := s) ha hx₀upper
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
  have hnorm := norm_integral_inv_mul_upperRosserBoundaryMassAux_le k (s := s) ha hx₀
  rw [Real.norm_eq_abs] at hnorm
  exact (le_abs_self _).trans hnorm

/-- A moving open interval can be handled by one fixed integrable envelope.
Only interior pointwise continuity is needed: the two endpoint slices are null. -/
private theorem continuousAt_screened_integral
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {p₀ : X} {l u : X → ℝ} {f : X → ℝ → ℝ} {c C : ℝ}
    (hl : ContinuousAt l p₀) (hu : ContinuousAt u p₀) (hC : 0 ≤ C)
    (hscreen : ∀ᶠ p in nhds p₀, c ≤ l p ∧ u p ≤ 1)
    (hmeas : ∀ p, MeasureTheory.StronglyMeasurable (f p))
    (hbound : ∀ᶠ p in nhds p₀, ∀ x ∈ Set.Ioo (l p) (u p), ‖f p x‖ ≤ C)
    (hcont : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.Ioo (l p₀) (u p₀) → ContinuousAt (fun p => f p x) p₀) :
    ContinuousAt (fun p => ∫ x in Set.Ioo (l p) (u p), f p x) p₀ := by
  let F := fun p => (Set.Ioo (l p) (u p)).indicator (f p)
  have hF : ContinuousAt (fun p => ∫ x, F p x) p₀ := by
    apply MeasureTheory.continuousAt_of_dominated
      (bound := (Set.Ioo c 1).indicator (fun _ : ℝ => C))
    · exact Filter.Eventually.of_forall fun p =>
        ((hmeas p).indicator measurableSet_Ioo).aestronglyMeasurable
    · filter_upwards [hscreen, hbound] with p hp hb
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioo (l p) (u p)
      · have hx' : x ∈ Set.Ioo c 1 := ⟨hp.1.trans_lt hx.1, hx.2.trans_le hp.2⟩
        simpa only [F, Set.indicator_of_mem hx, Set.indicator_of_mem hx'] using hb x hx
      · simpa only [F, Set.indicator_of_notMem hx, norm_zero] using
          Set.indicator_nonneg (fun _ _ => hC) x
    · exact (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioo
    · filter_upwards [hcont, MeasureTheory.volume.ae_ne (l p₀),
        MeasureTheory.volume.ae_ne (u p₀)] with x hxcont hxl hxu
      by_cases hx : x ∈ Set.Ioo (l p₀) (u p₀)
      · apply (hxcont hx).congr_of_eventuallyEq
        filter_upwards [hl (Iio_mem_nhds hx.1), hu (Ioi_mem_nhds hx.2)] with p hp hq
        exact Set.indicator_of_mem (show x ∈ Set.Ioo (l p) (u p) from ⟨hp, hq⟩) _
      · have hout : x < l p₀ ∨ u p₀ < x := by
          rcases lt_or_gt_of_ne hxl with h | h
          · exact Or.inl h
          · exact Or.inr (lt_of_le_of_ne (not_lt.mp (fun h' => hx ⟨h, h'⟩)) hxu.symm)
        apply (show (fun p => F p x) =ᶠ[nhds p₀] (fun _ => (0 : ℝ)) from ?_).continuousAt
        rcases hout with h | h
        · filter_upwards [hl (Ioi_mem_nhds h)] with p hp
          exact Set.indicator_of_notMem (fun hx => (hx.1.trans hp).false) _
        · filter_upwards [hu (Iio_mem_nhds h)] with p hp
          exact Set.indicator_of_notMem (fun hx => (hx.2.trans hp).false) _
  convert hF using 1
  funext p
  exact (MeasureTheory.integral_indicator measurableSet_Ioo).symm

/-- Joint continuity of the inner integral, with arbitrary continuous parameter
maps. This lemma is below the positive-depth induction and uses only an AE
continuity hypothesis for the preceding mass. -/
private theorem continuousAt_rosser_inner_parametric
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (k : ℕ) {p₀ : X} {s a b : X → ℝ}
    (ha : ContinuousAt a p₀) (hb : ContinuousAt b p₀)
    (ha₀ : 0 < a p₀) (hb₁ : ∀ᶠ p in nhds p₀, b p ≤ 1)
    (hcont : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.Ioo (a p₀) (b p₀) → ContinuousAt
        (fun p => upperRosserBoundaryMassAux k (s p - b p - x) (a p) x) p₀) :
    ContinuousAt (fun p => ∫ x in Set.Ioo (a p) (b p),
      x⁻¹ * upperRosserBoundaryMassAux k (s p - b p - x) (a p) x) p₀ := by
  let c := a p₀ / 2
  have hc : 0 < c := half_pos ha₀
  have hcut : ∀ᶠ p in nhds p₀, c ≤ a p := by
    have hlt : ∀ᶠ p in nhds p₀, c < a p :=
      ha (Ioi_mem_nhds (show c < a p₀ by dsimp [c]; linarith))
    exact hlt.mono fun _ h => h.le
  apply continuousAt_screened_integral ha hb
    (c := c) (C := c⁻¹ * (c⁻¹ * c⁻¹) ^ k) (by positivity) (hcut.and hb₁)
  · intro p
    exact measurable_id.inv.stronglyMeasurable.mul
      ((stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable
        (show Measurable (fun x : ℝ => ((s p - b p - x, a p), x)) by fun_prop))
  · filter_upwards [hcut, hb₁] with p hp hp₁ x hx
    have hxpos := hc.trans_le (hp.trans hx.1.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hxpos.le)
      (upperRosserBoundaryMassAux_nonneg k (hc.le.trans hp)))]
    exact mul_le_mul ((inv_le_inv₀ hxpos hc).2 (hp.trans hx.1.le))
      (upperRosserBoundaryMassAux_le_of_lower_bound k hc hp (hx.2.le.trans hp₁))
      (upperRosserBoundaryMassAux_nonneg k (hc.le.trans hp)) (inv_nonneg.mpr hc.le)
  · filter_upwards [hcont] with x hx hmem
    exact continuousAt_const.mul (hx hmem)

/-- The same screened dominated-integral theorem handles the outer recursive
step, without imposing continuity on the preceding depth-zero mass. -/
private theorem continuousAt_rosser_outer_parametric
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (k : ℕ) {p₀ : X} {s a u : X → ℝ}
    (ha : ContinuousAt a p₀) (hu : ContinuousAt u p₀)
    (ha₀ : 0 < a p₀) (hu₁ : ∀ᶠ p in nhds p₀, u p ≤ 1)
    (hinner : ∀ᵐ x₀ ∂MeasureTheory.volume,
      x₀ ∈ Set.Ioo (a p₀) (u p₀) → ContinuousAt
        (fun p => ∫ x₁ in Set.Ioo (a p) x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s p - x₀ - x₁) (a p) x₁) p₀) :
    ContinuousAt (fun p => ∫ x₀ in Set.Ioo (a p) (u p),
      x₀⁻¹ * ∫ x₁ in Set.Ioo (a p) x₀,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s p - x₀ - x₁) (a p) x₁) p₀ := by
  let c := a p₀ / 2
  have hc : 0 < c := half_pos ha₀
  have hcut : ∀ᶠ p in nhds p₀, c ≤ a p := by
    have hlt : ∀ᶠ p in nhds p₀, c < a p :=
      ha (Ioi_mem_nhds (show c < a p₀ by dsimp [c]; linarith))
    exact hlt.mono fun _ h => h.le
  apply continuousAt_screened_integral ha hu
    (c := c) (C := c⁻¹ * (c⁻¹ * (c⁻¹ * c⁻¹) ^ k)) (by positivity) (hcut.and hu₁)
  · intro p
    exact measurable_id.inv.stronglyMeasurable.mul
      ((stronglyMeasurable_integral_inv_mul_upperRosserBoundaryMassAux k).comp_measurable
        (show Measurable (fun x₀ : ℝ => ((s p, a p), x₀)) by fun_prop))
  · filter_upwards [hcut, hu₁] with p hp hp₁ x hx
    have hap : 0 < a p := hc.trans_le hp
    have hxpos : 0 < x := hap.trans hx.1
    have hinv : (a p)⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hap hc).2 hp
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    apply mul_le_mul ((inv_le_inv₀ hxpos hc).2 (hp.trans hx.1.le)) _ (norm_nonneg _)
      (inv_nonneg.mpr hc.le)
    exact (norm_integral_inv_mul_upperRosserBoundaryMassAux_le k hap
      (hx.2.le.trans hp₁)).trans (mul_le_mul hinv
        (pow_le_pow_left₀ (by positivity) (mul_le_mul hinv hinv (by positivity) (by positivity)) k)
        (by positivity) (by positivity))
  · filter_upwards [hinner] with x hx hmem
    exact continuousAt_const.mul (hx hmem)

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
  apply continuousAt_rosser_inner_parametric k continuousAt_const continuousAt_const ha
    (Filter.Eventually.of_forall fun _ => hx₀)
  have hcont' := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hcont
  filter_upwards [hcont'] with x hx hmem
  exact (hx hmem).comp (x := s)
    (show ContinuousAt (fun t : ℝ => t - x₀ - x) s by fun_prop)

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
  apply continuousAt_rosser_inner_parametric k continuousAt_snd continuousAt_const ha
    (Filter.Eventually.of_forall fun _ => hx₀)
  have hcont' := (MeasureTheory.ae_restrict_iff' measurableSet_Iio).mp hcont
  filter_upwards [hcont'] with x hx hmem
  exact hx (hmem.2.trans_le hx₀)

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
  simp_rw [upperRosserBoundaryMassAux_succ]
  apply continuousAt_rosser_outer_parametric k continuousAt_snd (by fun_prop) ha
    (Filter.Eventually.of_forall fun p => (min_le_left b (p.1 / 3)).trans hb)
  have hinner' := (MeasureTheory.ae_restrict_iff' measurableSet_Iio).mp hinner
  filter_upwards [hinner'] with x hx hmem
  exact hx ((hmem.2.trans_le (min_le_left _ _)).trans_le hb)

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

/-- Once the lower/level induction is available, all three parameters of the
inner integral can move together. The depth-zero case still excludes precisely
the two affine null slices; no positive-depth theorem is used at depth zero. -/
private theorem continuousAt_rosser_inner
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (k : ℕ) {p₀ : X} {s a b : X → ℝ}
    (hs : ContinuousAt s p₀) (ha : ContinuousAt a p₀) (hb : ContinuousAt b p₀)
    (ha₀ : 0 < a p₀) (hb₁ : ∀ᶠ p in nhds p₀, b p ≤ 1) :
    ContinuousAt (fun p => ∫ x in Set.Ioo (a p) (b p),
      x⁻¹ * upperRosserBoundaryMassAux k (s p - b p - x) (a p) x) p₀ := by
  have hb₀ : b p₀ ≤ 1 := hb₁.self_of_nhds
  apply continuousAt_rosser_inner_parametric k ha hb ha₀ hb₁
  cases k with
  | zero =>
      filter_upwards [MeasureTheory.volume.ae_ne (s p₀ - b p₀),
        MeasureTheory.volume.ae_ne (s p₀ - b p₀ - 3 * a p₀)] with x hx₀ hx₃ _
      exact (continuousAt_upperRosserBoundaryMassAux_zero_level_lower
        (s := s p₀ - b p₀ - x) (a := a p₀) (b := x) (by intro h; apply hx₀; linarith)
        (by intro h; apply hx₃; linarith)).comp
        (x := p₀) (((hs.sub hb).sub (continuousAt_const (y := x))).prodMk ha)
  | succ k =>
      filter_upwards with x hx
      exact (continuousAt_upperRosserBoundaryMassAux_level_lower_succ k
        (s := s p₀ - b p₀ - x) (a := a p₀) (b := x) ha₀ (hx.2.le.trans hb₀)).comp
        (x := p₀) (((hs.sub hb).sub (continuousAt_const (y := x))).prodMk ha)

/-- Clipping only the inherited upper face yields joint continuity on the full
open positive-lower-cutoff domain. Specializations below recover the unmodified
mass whenever the inherited upper face is at most one. -/
private theorem continuousAt_rosser_mass_joint
    (k : ℕ) {p : (ℝ × ℝ) × ℝ} (ha : 0 < p.1.2) :
    ContinuousAt (fun q : (ℝ × ℝ) × ℝ =>
      upperRosserBoundaryMassAux (k + 1) q.1.1 q.1.2 (min q.2 1)) p := by
  simp_rw [upperRosserBoundaryMassAux_succ]
  apply continuousAt_rosser_outer_parametric k
    (continuousAt_fst.snd) (by fun_prop) ha
    (Filter.Eventually.of_forall fun q =>
      (min_le_left (min q.2 1) (q.1.1 / 3)).trans (min_le_right q.2 1))
  filter_upwards with x hx
  exact continuousAt_rosser_inner k (continuousAt_fst.fst) (continuousAt_fst.snd)
    continuousAt_const ha (Filter.Eventually.of_forall fun _ =>
      hx.2.le.trans ((min_le_left _ _).trans (min_le_right _ _)))

/-- A single compact-box modulus controls the complete moving inner integral,
including reversed or coincident endpoints, where the open interval is empty. -/
private theorem rosser_inner_joint_modulus
    (k : ℕ) {s₀ s₁ c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0,
      ∀ p ∈ (Set.Icc s₀ s₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1,
      ∀ q ∈ (Set.Icc s₀ s₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1,
        dist p q < δ →
        |(∫ x in Set.Ioo p.1.2 p.2, x⁻¹ *
            upperRosserBoundaryMassAux k (p.1.1 - p.2 - x) p.1.2 x) -
          ∫ x in Set.Ioo q.1.2 q.2, x⁻¹ *
            upperRosserBoundaryMassAux k (q.1.1 - q.2 - x) q.1.2 x| < ε := by
  have hcont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      ∫ x in Set.Ioo p.1.2 p.2, x⁻¹ *
        upperRosserBoundaryMassAux k (p.1.1 - p.2 - x) p.1.2 x)
      ((Set.Icc s₀ s₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1) := by
    have hclip : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
        ∫ x in Set.Ioo p.1.2 (min p.2 1), x⁻¹ *
          upperRosserBoundaryMassAux k (p.1.1 - min p.2 1 - x) p.1.2 x)
        ((Set.Icc s₀ s₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1) := by
      intro p hp
      exact (continuousAt_rosser_inner k (continuousAt_fst.fst) (continuousAt_fst.snd)
        (continuousAt_snd.min continuousAt_const) (hc.trans_le hp.1.2.1)
        (Filter.Eventually.of_forall fun q => min_le_right q.2 1)).continuousWithinAt
    exact hclip.congr fun p hp => by simp only [min_eq_left hp.2.2]
  simpa only [Real.dist_eq] using Metric.uniformContinuousOn_iff.mp
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).uniformContinuousOn_of_continuous
      hcont) ε hε

/-- Restriction and continuous parameter substitution recover the original,
unclipped mass on any domain whose upper faces stay below one. -/
private theorem continuousOn_rosser_mass
    {X : Type*} [TopologicalSpace X] (k : ℕ) {S : Set X} {s a b : X → ℝ}
    (hs : ContinuousOn s S) (ha : ContinuousOn a S) (hb : ContinuousOn b S)
    (hapos : ∀ p ∈ S, 0 < a p) (hble : ∀ p ∈ S, b p ≤ 1) :
    ContinuousOn (fun p => upperRosserBoundaryMassAux (k + 1) (s p) (a p) (b p)) S := by
  have hclip : ContinuousOn
      (fun p => upperRosserBoundaryMassAux (k + 1) (s p) (a p) (min (b p) 1)) S := by
    intro p hp
    exact (continuousAt_rosser_mass_joint k
      (p := ((s p, a p), b p)) (hapos p hp)).comp_continuousWithinAt (x := p)
      (((hs p hp).prodMk (ha p hp)).prodMk (hb p hp))
  exact hclip.congr fun p hp => by simp only [min_eq_left (hble p hp)]

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
  simp_rw [upperRosserBoundaryMassAux_succ]
  apply continuousAt_rosser_outer_parametric k continuousAt_const (by fun_prop) ha
    (Filter.Eventually.of_forall fun t => (min_le_left b (t / 3)).trans hb)
  have hinner' := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hinner
  filter_upwards [hinner'] with x hx hmem
  exact hx ⟨hmem.1, hmem.2.trans_le (min_le_left _ _)⟩

/-- Every positive-depth recursive Rosser boundary mass is continuous in its
residual level.  At depth zero there are two affine jumps; after one peeled
pair, both jumps lie on null one-dimensional slices and dominated convergence
smooths them. -/
theorem continuous_upperRosserBoundaryMassAux_level_succ
    (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    Continuous (fun s => upperRosserBoundaryMassAux (k + 1) s a b) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (continuousAt_upperRosserBoundaryMassAux_level_lower_succ k (s := s) ha hb).comp
    (x := s)
    (continuousAt_id.prodMk continuousAt_const)

/-- The inner integral in one Rosser pair is jointly continuous in the residual
level and the peeled outer coordinate once the residual boundary mass has
positive depth.  Clipping the moving upper face at `1` gives a global dominated
convergence argument whose restriction is the desired ordered integral. -/
theorem continuousOn_integral_inv_mul_upperRosserBoundaryMassAux_outer_succ
    (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ x₁ in Set.Ioo a p.2,
      x₁⁻¹ * upperRosserBoundaryMassAux (k + 1) (p.1 - p.2 - x₁) a x₁)
      (Set.univ ×ˢ Set.Icc a 1) := by
  have hclip : Continuous (fun p : ℝ × ℝ => ∫ x in Set.Ioo a (min p.2 1),
      x⁻¹ * upperRosserBoundaryMassAux (k + 1) (p.1 - min p.2 1 - x) a x) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact continuousAt_rosser_inner (k + 1) continuousAt_fst continuousAt_const
      (continuousAt_snd.min continuousAt_const) ha
      (Filter.Eventually.of_forall fun q => min_le_right q.2 1)
  exact hclip.continuousOn.congr fun p hp => by simp only [min_eq_left hp.2.2]

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
      exact continuousOn_rosser_mass k continuousOn_const continuousOn_const continuousOn_id
        (fun _ _ => ha) (fun _ hb => hb.2)

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
vary jointly continuously on every compact screened rectangle. This is a
restriction of joint dominated-integral continuity; the depth-zero jumps have
already been handled on null slices in the foundational induction. -/
theorem continuousOn_upperRosserBoundaryMassAux_level_upper_succ
    (k : ℕ) {a r₀ r₁ : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun p : ℝ × ℝ => upperRosserBoundaryMassAux (k + 1) p.1 a p.2)
      (Set.Icc r₀ r₁ ×ˢ Set.Icc a 1) := by
  exact continuousOn_rosser_mass k continuousOn_fst continuousOn_const continuousOn_snd
    (fun _ _ => ha) (fun _ hp => hp.2.2)

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
the part where that face lies below the lower cutoff. At positive depth the mass
vanishes there; at depth zero it is independent of the inherited upper face. -/
theorem continuousOn_upperRosserBoundaryMassAux_upper_global
    (k : ℕ) {s a c : ℝ} (ha : 0 < a) :
    ContinuousOn (fun b => upperRosserBoundaryMassAux k s a b) (Set.Icc c 1) := by
  cases k with
  | zero =>
      simp only [upperRosserBoundaryMassAux_zero]
      fun_prop
  | succ k =>
      exact continuousOn_rosser_mass k continuousOn_const continuousOn_const continuousOn_id
        (fun _ _ => ha) (fun _ hb => hb.2)

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
  have hcont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 p.2)
      ((Set.Icc r₀ r₁ ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1) :=
    continuousOn_rosser_mass k (by fun_prop) (by fun_prop) continuousOn_snd
      (fun _ hp => hc.trans_le hp.1.2.1) (fun _ hp => hp.2.2)
  simpa only [Real.dist_eq] using Metric.uniformContinuousOn_iff.mp
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).uniformContinuousOn_of_continuous
      hcont) ε hε

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
  obtain ⟨δ, hδ, hmod⟩ := rosser_inner_joint_modulus (k + 1)
    (s₀ := s₀) (s₁ := s₁) hc hε
  refine ⟨δ, hδ, ?_⟩
  intro s x₀ l a hs hx₀ hl ha hla hwidth
  have hdist : dist ((s, l), x₀) ((s, a), x₀) < δ := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hla),
      sub_nonneg.mpr hla] using hwidth
  have hclose := hmod ((s, l), x₀) ⟨⟨hs, hl⟩, hx₀⟩
    ((s, a), x₀) ⟨⟨hs, ha⟩, hx₀⟩ hdist
  dsimp only at hclose
  linarith [(abs_lt.mp hclose).2]

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
  obtain ⟨δ, hδ, hmod⟩ := rosser_inner_joint_modulus (k + 1)
    (s₀ := s₀) (s₁ := s₁) hc hε
  refine ⟨δ, hδ, ?_⟩
  intro s a x₀ y₀ hs ha hx₀ hy₀ _hax hxy hwidth
  have hdist : dist ((s, a), y₀) ((s, a), x₀) < δ := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy), hδ] using hwidth
  have hclose := hmod ((s, a), y₀) ⟨⟨hs, ha⟩, hy₀⟩
    ((s, a), x₀) ⟨⟨hs, ha⟩, hx₀⟩ hdist
  dsimp only at hclose
  linarith [(abs_lt.mp hclose).2]

/-- The joint inner-integral modulus also covers a mesh cell crossing the
moving lower cutoff. Empty and coincident intervals need no separate strip
estimate because the moving-interval continuity theorem includes them. -/
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
  obtain ⟨δ, hδ, hmod⟩ := rosser_inner_joint_modulus (k + 1)
    (s₀ := s₀) (s₁ := s₁) hc hε
  refine ⟨δ, hδ, ?_⟩
  intro s a x₀ y₀ hs ha hx₀ hy₀ hxy hwidth
  have hdist : dist ((s, a), y₀) ((s, a), x₀) < δ := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy), hδ] using hwidth
  have hclose := hmod ((s, a), y₀) ⟨⟨hs, ha⟩, hy₀⟩
    ((s, a), x₀) ⟨⟨hs, ha⟩, hx₀⟩ hdist
  dsimp only at hclose
  linarith [(abs_lt.mp hclose).2]


end MathlibNt.SieveTheory.LinearSieve
