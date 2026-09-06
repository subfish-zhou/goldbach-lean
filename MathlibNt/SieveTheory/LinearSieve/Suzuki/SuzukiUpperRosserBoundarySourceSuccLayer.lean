import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserFiniteToContinuousProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132ExactParityTail

namespace MathlibNt.SieveTheory.LinearSieve

open MeasureTheory Set
open SuzukiFiniteContinuousLayers

noncomputable section

/-- Fubini reindexing on the open triangular region
`0 < a < b`, `a < x < u`.  The explicit integrability premise is the exact
hypothesis needed before the positive-depth upper Rosser source recursion can
be rearranged. -/
theorem triangular_integral_swap
    (F : ℝ → ℝ → ℝ) (b u : ℝ)
    (hF : MeasureTheory.Integrable
      (Function.uncurry fun a x =>
        ({p : ℝ × ℝ | p.1 ∈ Set.Ioo 0 b ∧ p.2 ∈ Set.Ioo p.1 u}).indicator
          (Function.uncurry F) (a, x)) (volume.prod volume)) :
    (∫ a in Set.Ioo 0 b, ∫ x in Set.Ioo a u, F a x) =
      ∫ x in Set.Ioo 0 u, ∫ a in Set.Ioo 0 (min b x), F a x := by
  let D : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Set.Ioo 0 b ∧ p.2 ∈ Set.Ioo p.1 u}
  change MeasureTheory.Integrable
    (Function.uncurry (fun a x => D.indicator (Function.uncurry F) (a, x)))
    (volume.prod volume) at hF
  have hswap := MeasureTheory.integral_integral_swap hF
  have hleft :
      (∫ a in Set.Ioo 0 b, ∫ x in Set.Ioo a u, F a x) =
        ∫ a, ∫ x, D.indicator (Function.uncurry F) (a, x) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with a
    by_cases ha : a ∈ Set.Ioo 0 b
    · simp only [Set.indicator_of_mem ha]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioo a u
      · simp [Set.indicator, D, ha.1, ha.2, hx.1, hx.2]
      · have hp : (a, x) ∉ D := fun h => hx h.2
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hp]
    · rw [show (Set.Ioo 0 b).indicator
          (fun a => ∫ x in Set.Ioo a u, F a x) a = 0 by
            simp [Set.indicator, ha]]
      apply Eq.symm
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with x
      have hp : (a, x) ∉ D := fun h => ha h.1
      rw [Set.indicator_of_notMem hp]
      rfl
  have hright :
      (∫ x, ∫ a, D.indicator (Function.uncurry F) (a, x)) =
        ∫ x in Set.Ioo 0 u, ∫ a in Set.Ioo 0 (min b x), F a x := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioo 0 u
    · simp only [Set.indicator_of_mem hx]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      by_cases ha : a ∈ Set.Ioo 0 (min b x)
      · simp [Set.indicator, D, ha.1,
          ha.2.trans_le (min_le_left _ _),
          ha.2.trans_le (min_le_right _ _), hx.2]
      · have hp : (a, x) ∉ D := by
          intro h
          exact ha ⟨h.1.1, lt_min h.1.2 h.2.1⟩
        rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem ha]
    · rw [show (Set.Ioo 0 u).indicator
          (fun x => ∫ a in Set.Ioo 0 (min b x), F a x) x = 0 by
            simp [Set.indicator, hx]]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with a
      have hp : (a, x) ∉ D := by
        intro h
        exact hx ⟨h.1.1.trans h.2.1, h.2.2⟩
      rw [Set.indicator_of_notMem hp]
      rfl
  exact hleft.trans (hswap.trans hright)

private theorem scale_mul_inv (hc : 0 < c) (x : ℝ) :
    c * (c * x)⁻¹ = x⁻¹ := by
  calc
    c * (c * x)⁻¹ = c * (x⁻¹ * c⁻¹) := by rw [mul_inv_rev]
    _ = (c * x⁻¹) * c⁻¹ := by rw [mul_assoc]
    _ = x⁻¹ * (c * c⁻¹) := by rw [mul_comm c x⁻¹, ← mul_assoc]
    _ = x⁻¹ := by rw [mul_inv_cancel₀ hc.ne', mul_one]

theorem upperRosserBoundaryMassAux_homogeneous
    (k : ℕ) {c s a b : ℝ} (hc : 0 < c) :
    upperRosserBoundaryMassAux k (c * s) (c * a) (c * b) =
      upperRosserBoundaryMassAux k s a b := by
  induction k generalizing s a b with
  | zero =>
      have hcond :
          (0 ≤ c * s ∧ c * s < 3 * (c * a)) ↔
            (0 ≤ s ∧ s < 3 * a) := by
        constructor <;> intro h <;> constructor <;> nlinarith [hc]
      simp [upperRosserBoundaryMassAux_zero, hcond]
  | succ k ih =>
      rw [upperRosserBoundaryMassAux_succ, upperRosserBoundaryMassAux_succ]
      have houter :
          min (c * b) ((c * s) / 3) = c * min b (s / 3) := by
        rw [show (c * s) / 3 = c * (s / 3) by ring, mul_min_of_nonneg _ _ hc.le]
      rw [houter]
      have hinner :
          ∀ y : ℝ,
            (∫ x in Set.Ioo (c * a) (c * y),
              x⁻¹ * upperRosserBoundaryMassAux k (c * s - c * y - x) (c * a) x) =
              ∫ x in Set.Ioo a y,
                x⁻¹ * upperRosserBoundaryMassAux k (s - y - x) a x := by
        intro y
        have himage :
            (fun x : ℝ => c * x) '' Set.Ioo a y = Set.Ioo (c * a) (c * y) := by
          simpa using image_mul_left_Ioo hc a y
        rw [← himage]
        rw [integral_image_eq_integral_abs_deriv_smul
          (s := Set.Ioo a y) (f := fun x : ℝ => c * x) (f' := fun _ => c)
          measurableSet_Ioo
          (fun x _ => (hasDerivAt_const_mul c).hasDerivWithinAt)
          (fun x _ z _ h => (strictMono_mul_left_of_pos hc).injective h)]
        refine setIntegral_congr_fun measurableSet_Ioo ?_
        intro x hx
        simp only [abs_of_pos hc, smul_eq_mul]
        calc
          c * ((c * x)⁻¹ * upperRosserBoundaryMassAux k (c * s - c * y - c * x) (c * a) (c * x)) =
              (c * (c * x)⁻¹) * upperRosserBoundaryMassAux k (c * s - c * y - c * x) (c * a) (c * x) := by
                rw [mul_assoc]
          _ = x⁻¹ * upperRosserBoundaryMassAux k (c * s - c * y - c * x) (c * a) (c * x) := by
                rw [scale_mul_inv hc x]
          _ = x⁻¹ * upperRosserBoundaryMassAux k (s - y - x) a x := by
                congr 1
                convert ih (s := s - y - x) (a := a) (b := x) using 1
                ring_nf
      have himage :
          (fun x : ℝ => c * x) '' Set.Ioo a (min b (s / 3)) =
            Set.Ioo (c * a) (c * min b (s / 3)) := by
        simpa using image_mul_left_Ioo hc a (min b (s / 3))
      rw [← himage]
      rw [integral_image_eq_integral_abs_deriv_smul
        (s := Set.Ioo a (min b (s / 3))) (f := fun x : ℝ => c * x) (f' := fun _ => c)
        measurableSet_Ioo
        (fun x _ => (hasDerivAt_const_mul c).hasDerivWithinAt)
        (fun x _ z _ h => (strictMono_mul_left_of_pos hc).injective h)]
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro x hx
      simp only [abs_of_pos hc, smul_eq_mul]
      calc
        c *
            ((c * x)⁻¹ *
              ∫ x₁ in Set.Ioo (c * a) (c * x),
                x₁⁻¹ * upperRosserBoundaryMassAux k (c * s - c * x - x₁) (c * a) x₁) =
            (c * (c * x)⁻¹) *
              ∫ x₁ in Set.Ioo (c * a) (c * x),
                x₁⁻¹ * upperRosserBoundaryMassAux k (c * s - c * x - x₁) (c * a) x₁ := by
              rw [mul_assoc]
        _ = x⁻¹ *
              ∫ x₁ in Set.Ioo (c * a) (c * x),
                x₁⁻¹ * upperRosserBoundaryMassAux k (c * s - c * x - x₁) (c * a) x₁ := by
              rw [scale_mul_inv hc x]
        _ = x⁻¹ * ∫ x₁ in Set.Ioo a x, x₁⁻¹ * upperRosserBoundaryMassAux k (s - x - x₁) a x₁ := by
              rw [hinner x]

/-- The packaged source integral with inherited upper face `b`. -/
noncomputable def upperRosserBoundarySourceIntegral
    (k : ℕ) (s b : ℝ) : ℝ :=
  ∫ a in Set.Ioo 0 b,
    a⁻¹ * a⁻¹ * upperRosserBoundaryMassAux k s a b

@[simp] theorem upperRosserBoundarySourceIntegral_one
    (k : ℕ) (s : ℝ) :
    upperRosserBoundarySourceIntegral k s 1 =
      ∫ a in Set.Ioo 0 1,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a := by
  rfl

theorem upperRosserBoundarySourceIntegral_homogeneous
    (k : ℕ) {c s b : ℝ} (hc : 0 < c) :
    upperRosserBoundarySourceIntegral k (c * s) (c * b) =
      c⁻¹ * upperRosserBoundarySourceIntegral k s b := by
  unfold upperRosserBoundarySourceIntegral
  have himage :
      (fun x : ℝ => c * x) '' Set.Ioo (0 : ℝ) b = Set.Ioo (0 : ℝ) (c * b) := by
    simpa [zero_mul] using image_mul_left_Ioo hc (0 : ℝ) b
  rw [← himage]
  rw [integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0 : ℝ) b) (f := fun x : ℝ => c * x) (f' := fun _ => c)
    measurableSet_Ioo
    (fun x _ => (hasDerivAt_const_mul c).hasDerivWithinAt)
    (fun x _ y _ h => (strictMono_mul_left_of_pos hc).injective h)]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun
    (s := Set.Ioo (0 : ℝ) b)
    (g := fun x : ℝ =>
      c⁻¹ * (x⁻¹ * x⁻¹ * upperRosserBoundaryMassAux k s x b))
  · exact measurableSet_Ioo
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  simp only [abs_of_pos hc, smul_eq_mul]
  calc
    c *
        ((c * x)⁻¹ * (c * x)⁻¹ *
          upperRosserBoundaryMassAux k (c * s) (c * x) (c * b)) =
        c * ((c * x)⁻¹ * (c * x)⁻¹ * upperRosserBoundaryMassAux k s x b) := by
          rw [upperRosserBoundaryMassAux_homogeneous k hc]
    _ = c⁻¹ * (x⁻¹ * x⁻¹ * upperRosserBoundaryMassAux k s x b) := by
          field_simp [hc.ne', hx0]

theorem upperRosserBoundarySourceIntegral_normalize
    (k : ℕ) {s b : ℝ} (hb : 0 < b) :
    upperRosserBoundarySourceIntegral k s b =
      b⁻¹ * upperRosserBoundarySourceIntegral k (s / b) 1 := by
  calc
    upperRosserBoundarySourceIntegral k s b =
        upperRosserBoundarySourceIntegral k (b * (s / b)) (b * 1) := by
          congr 2
          · field_simp [hb.ne']
          · ring
    _ = b⁻¹ * upperRosserBoundarySourceIntegral k (s / b) 1 := by
      simpa [div_eq_mul_inv] using
    (upperRosserBoundarySourceIntegral_homogeneous
      k (c := b) (s := s / b) (b := 1) hb)

theorem upperRosserBoundarySourceIntegral_eq_zero_of_upper_le_support
    (k : ℕ) {s b : ℝ} (hs : 0 ≤ s)
    (hb : b ≤ s / 3 ^ (k + 1)) :
    upperRosserBoundarySourceIntegral k s b = 0 := by
  unfold upperRosserBoundarySourceIntegral
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
  rw [upperRosserBoundaryMassAux_eq_zero_of_terminal_le k hs (ha.2.le.trans hb)]
  simp

theorem upperRosserBoundarySourceIntegral_eq_integral_of_lower_le_support
    (k : ℕ) {s c b : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcs : c ≤ s / 3 ^ (k + 1)) :
    upperRosserBoundarySourceIntegral k s b =
      ∫ a in Set.Ioo c b,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMassAux k s a b := by
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioo
  · intro a ha
    exact ⟨hc.trans_lt ha.1, ha.2⟩
  · intro a ha
    have hale : a ≤ s / 3 ^ (k + 1) := by
      exact le_of_not_gt fun hlt => ha.2 ⟨hcs.trans_lt hlt, ha.1.2⟩
    rw [upperRosserBoundaryMassAux_eq_zero_of_terminal_le k hs hale]
    simp


/-- The first positive-depth triangular Fubini kernel is genuinely integrable.
The proof uses the exact recursive support cutoff to remove the singular face
`a = 0`, then a uniform finite-depth bound on the remaining compact triangle. -/
theorem integrable_outer_triangle_upperRosserBoundaryMassAux
    (k : ℕ) {s b : ℝ} (hs : 3 / 2 ≤ s) (hb : b ≤ 1) :
    MeasureTheory.Integrable
      (({p : ℝ × ℝ |
          p.1 ∈ Set.Ioo 0 b ∧ p.2 ∈ Set.Ioo p.1 (min b (s / 3))}).indicator
        (Function.uncurry fun a x₀ =>
          a⁻¹ * a⁻¹ *
            (x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
              x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁)))
      (volume.prod volume) := by
  let D : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Set.Ioo 0 b ∧ p.2 ∈ Set.Ioo p.1 (min b (s / 3))}
  let G : ℝ × ℝ → ℝ := fun p =>
    p.1⁻¹ * p.1⁻¹ *
      (p.2⁻¹ * ∫ x₁ in Set.Ioo p.1 p.2,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - p.2 - x₁) p.1 x₁)
  change MeasureTheory.Integrable (D.indicator G) (volume.prod volume)
  have hDmeas : MeasurableSet D := by
    dsimp only [D]
    exact
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_const)).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd
          (measurable_const.min (measurable_const.div_const 3))))
  have hDsub : D ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le.trans hb⟩,
      ⟨hp.1.1.le.trans hp.2.1.le,
        hp.2.2.le.trans ((min_le_left _ _).trans hb)⟩⟩
  have hfinite : (volume.prod volume) D < ⊤ :=
    lt_of_le_of_lt (measure_mono hDsub)
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  have hinnerMeas : StronglyMeasurable (fun p : ℝ × ℝ =>
      ∫ x₁ in Set.Ioo p.1 p.2,
        x₁⁻¹ * upperRosserBoundaryMassAux k (s - p.2 - x₁) p.1 x₁) := by
    have h :=
      (stronglyMeasurable_integral_inv_mul_upperRosserBoundaryMassAux k).comp_measurable
        (show Measurable (fun p : ℝ × ℝ => ((s, p.1), p.2)) by fun_prop)
    convert h using 1
    funext p
    rfl
  have hGmeas : StronglyMeasurable G := by
    exact ((measurable_fst.inv.stronglyMeasurable.mul
      measurable_fst.inv.stronglyMeasurable).mul
        (measurable_snd.inv.stronglyMeasurable.mul hinnerMeas))
  let c : ℝ := 1 / (2 * 3 ^ (k + 1))
  let C : ℝ := (c⁻¹ * c⁻¹) ^ (k + 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hGD : IntegrableOn G D := by
    apply IntegrableOn.of_bound hfinite hGmeas.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hDmeas] with p hp
    rcases hp with ⟨ha, hx₀⟩
    have hx₀s : p.2 ≤ s / 3 := hx₀.2.le.trans (min_le_right _ _)
    have hx₀one : p.2 ≤ 1 := hx₀.2.le.trans ((min_le_left _ _).trans hb)
    by_cases hca : c < p.1
    · have haPos : 0 < p.1 := hc.trans hca
      have hx₀pos : 0 < p.2 := haPos.trans hx₀.1
      have haInv : p.1⁻¹ ≤ c⁻¹ := (inv_le_inv₀ haPos hc).2 hca.le
      have hx₀Inv : p.2⁻¹ ≤ c⁻¹ :=
        (inv_le_inv₀ hx₀pos hc).2 (hca.trans hx₀.1).le
      have hinnerNorm :
          ‖∫ x₁ in Set.Ioo p.1 p.2,
              x₁⁻¹ * upperRosserBoundaryMassAux k
                (s - p.2 - x₁) p.1 x₁‖ ≤
            c⁻¹ * (c⁻¹ * c⁻¹) ^ k := by
        calc
          ‖∫ x₁ in Set.Ioo p.1 p.2,
              x₁⁻¹ * upperRosserBoundaryMassAux k
                (s - p.2 - x₁) p.1 x₁‖ ≤
              (c⁻¹ * (c⁻¹ * c⁻¹) ^ k) *
                volume.real (Set.Ioo p.1 p.2) := by
            apply norm_setIntegral_le_of_norm_le_const_ae
            · rw [Real.volume_Ioo]
              exact ENNReal.ofReal_lt_top
            · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
              have hx₁pos : 0 < x₁ := haPos.trans hx₁.1
              have hx₁Inv : x₁⁻¹ ≤ c⁻¹ :=
                (inv_le_inv₀ hx₁pos hc).2 (hca.trans hx₁.1).le
              have hmass := upperRosserBoundaryMassAux_le_of_lower_bound
                k (s := s - p.2 - x₁) hc hca.le (hx₁.2.le.trans hx₀one)
              have hnonneg := upperRosserBoundaryMassAux_nonneg
                k (s := s - p.2 - x₁) (b := x₁) haPos.le
              rw [Real.norm_eq_abs, abs_of_nonneg
                (mul_nonneg (inv_nonneg.mpr hx₁pos.le) hnonneg)]
              exact mul_le_mul hx₁Inv hmass hnonneg (inv_nonneg.mpr hc.le)
          _ ≤ c⁻¹ * (c⁻¹ * c⁻¹) ^ k := by
            apply mul_le_of_le_one_right
            · positivity
            · rw [Measure.real_def, Real.volume_Ioo,
                ENNReal.toReal_ofReal (sub_nonneg.mpr hx₀.1.le)]
              linarith
      rw [show G p = p.1⁻¹ * p.1⁻¹ * (p.2⁻¹ *
          ∫ x₁ in Set.Ioo p.1 p.2,
            x₁⁻¹ * upperRosserBoundaryMassAux k
              (s - p.2 - x₁) p.1 x₁) by rfl,
        Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (inv_pos.mpr haPos), abs_of_pos (inv_pos.mpr hx₀pos)]
      calc
        p.1⁻¹ * p.1⁻¹ * (p.2⁻¹ * ‖∫ x₁ in Set.Ioo p.1 p.2,
            x₁⁻¹ * upperRosserBoundaryMassAux k
              (s - p.2 - x₁) p.1 x₁‖) ≤
            c⁻¹ * c⁻¹ * (c⁻¹ * (c⁻¹ * (c⁻¹ * c⁻¹) ^ k)) := by
          gcongr
        _ = C := by
          dsimp [C]
          rw [pow_succ, pow_succ]
          ring
    · have hac : p.1 ≤ c := le_of_not_gt hca
      have hinnerZero : (∫ x₁ in Set.Ioo p.1 p.2,
          x₁⁻¹ * upperRosserBoundaryMassAux k
            (s - p.2 - x₁) p.1 x₁) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
        have hmass : upperRosserBoundaryMassAux k
            (s - p.2 - x₁) p.1 x₁ = 0 := by
          by_contra hne
          have := upperRosserBoundaryMassAux_ne_zero_outer_lower
            k hs hx₀s hx₁.2 hne
          exact (not_lt_of_ge hac) this
        simp [hmass]
      rw [show G p = p.1⁻¹ * p.1⁻¹ * (p.2⁻¹ *
          ∫ x₁ in Set.Ioo p.1 p.2,
            x₁⁻¹ * upperRosserBoundaryMassAux k
              (s - p.2 - x₁) p.1 x₁) by rfl,
        hinnerZero]
      simp only [mul_zero, norm_zero]
      dsimp [C]
      positivity
  exact hGD.integrable_indicator hDmeas


/-- The outer source integral after unfolding one Rosser pair, with the first
triangular Fubini swap justified by the preceding strict integrability theorem. -/
theorem upperRosserBoundarySourceIntegral_succ_outer_swap
    (k : ℕ) {s b : ℝ} (hs : 3 / 2 ≤ s) (hb : b ≤ 1) :
    upperRosserBoundarySourceIntegral (k + 1) s b =
      ∫ x₀ in Set.Ioo 0 (min b (s / 3)),
        ∫ a in Set.Ioo 0 (min b x₀),
          a⁻¹ * a⁻¹ *
            (x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
              x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) := by
  unfold upperRosserBoundarySourceIntegral
  rw [show (fun a => a⁻¹ * a⁻¹ * upperRosserBoundaryMassAux (k + 1) s a b) =
      fun a => a⁻¹ * a⁻¹ *
        (∫ x₀ in Set.Ioo a (min b (s / 3)),
          x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
            x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) by
    funext a
    rw [upperRosserBoundaryMassAux_succ]]
  calc
    (∫ a in Set.Ioo 0 b,
        a⁻¹ * a⁻¹ *
          (∫ x₀ in Set.Ioo a (min b (s / 3)),
            x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
              x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁)) =
      ∫ a in Set.Ioo 0 b,
        ∫ x₀ in Set.Ioo a (min b (s / 3)),
          a⁻¹ * a⁻¹ *
            (x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
              x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro a ha
        dsimp only
        rw [← integral_const_mul]
    _ = _ := triangular_integral_swap
      (fun a x₀ => a⁻¹ * a⁻¹ *
        (x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁))
      b (min b (s / 3))
      (integrable_outer_triangle_upperRosserBoundaryMassAux k hs hb)

/-- For every outer coordinate, the remaining `(a,x₁)` triangle is integrable.
This is the strict integrability input for the second Fubini rearrangement. -/
theorem integrable_inner_triangle_upperRosserBoundaryMassAux
    (k : ℕ) {s b x₀ : ℝ} (hs : 3 / 2 ≤ s)
    (hx₀s : x₀ ≤ s / 3) (hx₀one : x₀ ≤ 1) :
    MeasureTheory.Integrable
      (({p : ℝ × ℝ |
          p.1 ∈ Set.Ioo 0 (min b x₀) ∧ p.2 ∈ Set.Ioo p.1 x₀}).indicator
        (Function.uncurry fun a x₁ =>
          a⁻¹ * a⁻¹ *
            (x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁)))
      (volume.prod volume) := by
  let D : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Set.Ioo 0 (min b x₀) ∧ p.2 ∈ Set.Ioo p.1 x₀}
  let G : ℝ × ℝ → ℝ := fun p =>
    p.1⁻¹ * p.1⁻¹ *
      (p.2⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - p.2) p.1 p.2)
  change MeasureTheory.Integrable (D.indicator G) (volume.prod volume)
  have hDmeas : MeasurableSet D := by
    dsimp only [D]
    exact
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst (measurable_const.min measurable_const))).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hDsub : D ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1.1.le,
      hp.1.2.le.trans ((min_le_right _ _).trans hx₀one)⟩,
      ⟨hp.1.1.le.trans hp.2.1.le, hp.2.2.le.trans hx₀one⟩⟩
  have hfinite : (volume.prod volume) D < ⊤ :=
    lt_of_le_of_lt (measure_mono hDsub)
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  have hmassMeas : StronglyMeasurable (fun p : ℝ × ℝ =>
      upperRosserBoundaryMassAux k (s - x₀ - p.2) p.1 p.2) := by
    have h := (stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable
      (show Measurable (fun p : ℝ × ℝ => ((s - x₀ - p.2, p.1), p.2)) by fun_prop)
    convert h using 1
    funext p
    rfl
  have hGmeas : StronglyMeasurable G := by
    exact ((measurable_fst.inv.stronglyMeasurable.mul
      measurable_fst.inv.stronglyMeasurable).mul
        (measurable_snd.inv.stronglyMeasurable.mul hmassMeas))
  let c : ℝ := 1 / (2 * 3 ^ (k + 1))
  let C : ℝ := c⁻¹ * c⁻¹ * (c⁻¹ * (c⁻¹ * c⁻¹) ^ k)
  have hc : 0 < c := by dsimp [c]; positivity
  have hGD : IntegrableOn G D := by
    apply IntegrableOn.of_bound hfinite hGmeas.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hDmeas] with p hp
    rcases hp with ⟨ha, hx₁⟩
    by_cases hca : c < p.1
    · have haPos : 0 < p.1 := hc.trans hca
      have hx₁pos : 0 < p.2 := haPos.trans hx₁.1
      have haInv : p.1⁻¹ ≤ c⁻¹ := (inv_le_inv₀ haPos hc).2 hca.le
      have hx₁Inv : p.2⁻¹ ≤ c⁻¹ :=
        (inv_le_inv₀ hx₁pos hc).2 (hca.trans hx₁.1).le
      have hmass := upperRosserBoundaryMassAux_le_of_lower_bound
        k (s := s - x₀ - p.2) hc hca.le (hx₁.2.le.trans hx₀one)
      have hnonneg := upperRosserBoundaryMassAux_nonneg
        k (s := s - x₀ - p.2) (b := p.2) haPos.le
      rw [show G p = p.1⁻¹ * p.1⁻¹ *
          (p.2⁻¹ * upperRosserBoundaryMassAux k
            (s - x₀ - p.2) p.1 p.2) by rfl,
        Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg (inv_nonneg.mpr haPos.le)
            (inv_nonneg.mpr haPos.le))
            (mul_nonneg (inv_nonneg.mpr hx₁pos.le) hnonneg))]
      dsimp only [C]
      gcongr
    · have hac : p.1 ≤ c := le_of_not_gt hca
      have hmass : upperRosserBoundaryMassAux k
          (s - x₀ - p.2) p.1 p.2 = 0 := by
        by_contra hne
        have := upperRosserBoundaryMassAux_ne_zero_outer_lower
          k hs hx₀s hx₁.2 hne
        exact (not_lt_of_ge hac) this
      rw [show G p = p.1⁻¹ * p.1⁻¹ *
          (p.2⁻¹ * upperRosserBoundaryMassAux k
            (s - x₀ - p.2) p.1 p.2) by rfl,
        hmass]
      simp only [mul_zero, norm_zero]
      dsimp [C]
      positivity
  exact hGD.integrable_indicator hDmeas

/-- After the second Fubini swap, the innermost `a`-integral is exactly the
source package with inherited upper face `x₁`. -/
theorem upperRosserBoundarySourceIntegral_succ_second_swap
    (k : ℕ) {s b : ℝ} (hs : 3 / 2 ≤ s) (hb : b ≤ 1) :
    upperRosserBoundarySourceIntegral (k + 1) s b =
      ∫ x₀ in Set.Ioo 0 (min b (s / 3)),
        x₀⁻¹ * ∫ x₁ in Set.Ioo 0 x₀,
          x₁⁻¹ * upperRosserBoundarySourceIntegral k (s - x₀ - x₁) x₁ := by
  rw [upperRosserBoundarySourceIntegral_succ_outer_swap k hs hb]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x₀ hx₀
  have hx₀s : x₀ ≤ s / 3 :=
    hx₀.2.le.trans (min_le_right _ _)
  have hx₀one : x₀ ≤ 1 :=
    hx₀.2.le.trans ((min_le_left _ _).trans hb)
  have hswap := triangular_integral_swap
    (fun a x₁ => a⁻¹ * a⁻¹ *
      (x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁))
    (min b x₀) x₀
    (integrable_inner_triangle_upperRosserBoundaryMassAux
      (b := b) k hs hx₀s hx₀one)
  calc
    (∫ a in Set.Ioo 0 (min b x₀),
        a⁻¹ * a⁻¹ *
          (x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
            x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁)) =
      x₀⁻¹ * ∫ a in Set.Ioo 0 (min b x₀),
        ∫ x₁ in Set.Ioo a x₀,
          a⁻¹ * a⁻¹ *
            (x₁⁻¹ * upperRosserBoundaryMassAux k
              (s - x₀ - x₁) a x₁) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro a ha
        dsimp only
        calc
          a⁻¹ * a⁻¹ *
              (x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
                x₁⁻¹ * upperRosserBoundaryMassAux k
                  (s - x₀ - x₁) a x₁) =
              x₀⁻¹ * (a⁻¹ * a⁻¹ *
                ∫ x₁ in Set.Ioo a x₀,
                  x₁⁻¹ * upperRosserBoundaryMassAux k
                    (s - x₀ - x₁) a x₁) := by ring
          _ = x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
              a⁻¹ * a⁻¹ *
                (x₁⁻¹ * upperRosserBoundaryMassAux k
                  (s - x₀ - x₁) a x₁) := by
            congr 1
            rw [← integral_const_mul]
    _ = x₀⁻¹ * ∫ x₁ in Set.Ioo 0 x₀,
        ∫ a in Set.Ioo 0 (min (min b x₀) x₁),
          a⁻¹ * a⁻¹ *
            (x₁⁻¹ * upperRosserBoundaryMassAux k
              (s - x₀ - x₁) a x₁) := congrArg (fun z => x₀⁻¹ * z) hswap
    _ = x₀⁻¹ * ∫ x₁ in Set.Ioo 0 x₀,
        x₁⁻¹ * upperRosserBoundarySourceIntegral k (s - x₀ - x₁) x₁ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x₁ hx₁
      dsimp only
      have hx₁b : x₁ ≤ b :=
        hx₁.2.le.trans (hx₀.2.le.trans (min_le_left _ _))
      have hmin : min (min b x₀) x₁ = x₁ := by
        rw [min_eq_right (le_min hx₁b hx₁.2.le)]
      rw [hmin]
      unfold upperRosserBoundarySourceIntegral
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro a ha
      ring

/-- The first strict reciprocal substitution, after homogeneity normalizes the
inherited upper face: `v = A / x` sends `(0,x₀)` to `(A/x₀,∞)`. -/
theorem integral_inv_mul_upperRosserBoundarySourceIntegral_change_variables
    (k : ℕ) {A x₀ : ℝ} (hA : 0 < A) (hx₀ : 0 < x₀) :
    (∫ x in Set.Ioo 0 x₀,
      x⁻¹ * upperRosserBoundarySourceIntegral k (A - x) x) =
      A⁻¹ * ∫ v in Set.Ioi (A / x₀),
        upperRosserBoundarySourceIntegral k (v - 1) 1 := by
  let f : ℝ → ℝ := fun v => A / v
  have hlower : 0 < A / x₀ := div_pos hA hx₀
  have himage : f '' Set.Ioi (A / x₀) = Set.Ioo 0 x₀ := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hvpos : 0 < v := hlower.trans hv
      constructor
      · exact div_pos hA hvpos
      · rw [div_lt_iff₀ hvpos]
        have hv' : A / x₀ < v := hv
        rw [div_lt_iff₀ hx₀] at hv'
        simpa [mul_comm] using hv'
    · intro hx
      refine ⟨A / x, ?_, ?_⟩
      · change A / x₀ < A / x
        exact (div_lt_div_iff_of_pos_left hA hx₀ hx.1).2 hx.2
      · dsimp only [f]
        field_simp [hA.ne', hx.1.ne']
  rw [← himage]
  rw [integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (A / x₀)) (f := f)
    (f' := fun v => A * (-(v ^ 2)⁻¹)) measurableSet_Ioi]
  · rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hlower.trans hv
    have hfvpos : 0 < f v := div_pos hA hvpos
    have hnormalize := upperRosserBoundarySourceIntegral_normalize
      k (s := A - f v) (b := f v) hfvpos
    simp only [smul_eq_mul]
    rw [hnormalize]
    dsimp only [f]
    have hvInvSq : 0 < (v ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hvpos)
    rw [abs_of_neg (mul_neg_of_pos_of_neg hA (neg_neg_of_pos hvInvSq))]
    have harg : (A - A / v) / (A / v) = v - 1 := by
      field_simp [hA.ne', hvpos.ne']
    rw [harg]
    field_simp [hA.ne', hvpos.ne']
  · intro v hv
    have hvpos : 0 < v := hlower.trans hv
    simpa only [f, div_eq_mul_inv] using
      ((hasDerivAt_inv hvpos.ne').const_mul A).hasDerivWithinAt
  · intro v hv w hw hvw
    have hvpos : 0 < v := hlower.trans hv
    have hwpos : 0 < w := hlower.trans hw
    dsimp only [f] at hvw
    field_simp [hvpos.ne', hwpos.ne'] at hvw
    nlinarith [hA]

/-- The successor source after the first strict variable replacement.  The
remaining inner integrand now has normalized upper face `1`, ready for the
first `κ = 1` Suzuki recursion. -/
theorem upperRosserBoundarySourceIntegral_succ_first_change_variables
    (k : ℕ) {s b : ℝ} (hs : 3 / 2 ≤ s) (hb : b ≤ 1) :
    upperRosserBoundarySourceIntegral (k + 1) s b =
      ∫ x₀ in Set.Ioo 0 (min b (s / 3)),
        x₀⁻¹ * ((s - x₀)⁻¹ *
          ∫ v in Set.Ioi ((s - x₀) / x₀),
            upperRosserBoundarySourceIntegral k (v - 1) 1) := by
  rw [upperRosserBoundarySourceIntegral_succ_second_swap k hs hb]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x₀ hx₀
  have hx₀s : x₀ ≤ s / 3 := hx₀.2.le.trans (min_le_right _ _)
  have hspos : 0 < s := by linarith
  have hA : 0 < s - x₀ := by
    have hsdiv : s / 3 < s := by linarith
    linarith
  dsimp only
  rw [integral_inv_mul_upperRosserBoundarySourceIntegral_change_variables
    k hA hx₀.1]

/-- The second strict reciprocal substitution `x₀ = s / t`.  Together with the
preceding `v = (s - x₀) / x₁` substitution, this is exactly the two-step
`κ = 1` Suzuki kernel, before its support is truncated to finite intervals. -/
theorem upperRosserBoundarySourceIntegral_succ_second_change_variables
    (k : ℕ) {s : ℝ} (hs : 3 / 2 ≤ s) :
    upperRosserBoundarySourceIntegral (k + 1) s 1 =
      s⁻¹ * ∫ t in Set.Ioi (s / min 1 (s / 3)),
        (t - 1)⁻¹ * ∫ v in Set.Ioi (t - 1),
          upperRosserBoundarySourceIntegral k (v - 1) 1 := by
  rw [upperRosserBoundarySourceIntegral_succ_first_change_variables
    k hs (by norm_num)]
  let u : ℝ := min 1 (s / 3)
  let f : ℝ → ℝ := fun t => s / t
  have hspos : 0 < s := by linarith
  have hupos : 0 < u := by
    dsimp only [u]
    exact lt_min (by norm_num) (div_pos hspos (by norm_num))
  have hlower : 0 < s / u := div_pos hspos hupos
  have himage : f '' Set.Ioi (s / u) = Set.Ioo 0 u := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htpos : 0 < t := hlower.trans ht
      constructor
      · exact div_pos hspos htpos
      · rw [div_lt_iff₀ htpos]
        have ht' : s / u < t := ht
        rw [div_lt_iff₀ hupos] at ht'
        simpa [mul_comm] using ht'
    · intro hx
      refine ⟨s / x, ?_, ?_⟩
      · change s / u < s / x
        exact (div_lt_div_iff_of_pos_left hspos hupos hx.1).2 hx.2
      · dsimp only [f]
        field_simp [hspos.ne', hx.1.ne']
  change (∫ x₀ in Set.Ioo 0 u,
      x₀⁻¹ * ((s - x₀)⁻¹ *
        ∫ v in Set.Ioi ((s - x₀) / x₀),
          upperRosserBoundarySourceIntegral k (v - 1) 1)) = _
  rw [← himage]
  rw [integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (s / u)) (f := f)
    (f' := fun t => s * (-(t ^ 2)⁻¹)) measurableSet_Ioi]
  · rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := hlower.trans ht
    have htm1pos : 0 < t - 1 := by
      have huone : u ≤ 1 := by dsimp [u]; exact min_le_left _ _
      have hst : s / u < t := ht
      have hsule : 1 ≤ s / u := (le_div_iff₀ hupos).2 (by
        have hsone : 1 ≤ s := by linarith
        simpa only [one_mul] using huone.trans hsone)
      linarith
    simp only [smul_eq_mul]
    dsimp only [f]
    have htInvSq : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos htpos)
    rw [abs_of_neg (mul_neg_of_pos_of_neg hspos (neg_neg_of_pos htInvSq))]
    have harg : (s - s / t) / (s / t) = t - 1 := by
      field_simp [hspos.ne', htpos.ne']
    rw [harg]
    field_simp [hspos.ne', htpos.ne', htm1pos.ne']
  · intro t ht
    have htpos : 0 < t := hlower.trans ht
    simpa only [f, div_eq_mul_inv] using
      ((hasDerivAt_inv htpos.ne').const_mul s).hasDerivWithinAt
  · intro t ht w hw htw
    have htpos : 0 < t := hlower.trans ht
    have hwpos : 0 < w := hlower.trans hw
    dsimp only [f] at htw
    field_simp [htpos.ne', hwpos.ne'] at htw
    nlinarith [hspos]

private theorem recursion_endpoint
  (k : ℕ) {s : ℝ} (hs : 3 / 2 ≤ s)
  (hssupp : s ≤ 2 + (2 * (k + 1) + 1 : ℕ)) :
    s / min 1 (s / 3) = recursionLower 2 s (2 * (k + 1) + 1) := by
  have hspos : 0 < s := by linarith
  have heps : sourceEpsilon (2 * (k + 1) + 1) = 1 := by
    unfold sourceEpsilon
    omega
  rw [recursionLower, heps]
  have hcap : max s (2 + (1 : ℕ)) ≤ 2 + (2 * (k + 1) + 1 : ℕ) := by
    rw [max_le_iff]
    constructor
    · exact hssupp
    · norm_num [Nat.cast_add, Nat.cast_mul]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
  rw [min_eq_left hcap]
  norm_num only [Nat.cast_one]
  by_cases hs3 : s ≤ 3
  · rw [max_eq_right hs3]
    have hsdiv : s / 3 ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 3)).2 hs3
    rw [min_eq_right hsdiv]
    field_simp [hspos.ne']
  · have h3s : 3 ≤ s := le_of_not_ge hs3
    rw [max_eq_left h3s]
    have hone : 1 ≤ s / 3 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      norm_num
      exact h3s
    rw [min_eq_left hone]
    simp

/-- On the upper fundamental-lemma window, the reciprocal image of the cubic
outer face is exactly the lower endpoint in the odd Suzuki recursion. -/
theorem div_min_one_div_three_eq_recursionLower_odd
    (k : ℕ) {s : ℝ} (hs : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    s / min 1 (s / 3) = recursionLower 2 s (2 * (k + 1) + 1) := by
  apply recursion_endpoint k hs
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The second reciprocal substitution with its lower endpoint written in the
literal first `suzukiLayer_succ_succ` form.  The only remaining difference from
the twice-recursed Suzuki layer is replacement of the two improper tails by
their finite support intervals and identification of the residual source. -/
theorem upperRosserBoundarySourceIntegral_succ_two_suzuki_kernel_shape
    (k : ℕ) {s : ℝ} (hs : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    upperRosserBoundarySourceIntegral (k + 1) s 1 =
      s⁻¹ * ∫ t in Set.Ioi (recursionLower 2 s (2 * (k + 1) + 1)),
        (t - 1)⁻¹ * ∫ v in Set.Ioi (t - 1),
          upperRosserBoundarySourceIntegral k (v - 1) 1 := by
  rw [upperRosserBoundarySourceIntegral_succ_second_change_variables k hs,
    div_min_one_div_three_eq_recursionLower_odd k hs hshi]

/-- Unfolding the target odd Suzuki layer twice gives the finite-interval kernel
which the preceding source formula must match. -/
theorem suzukiLayer_one_two_odd_succ_two_step_kernel
    (k : ℕ) (s : ℝ) :
    suzukiLayer 1 2 (2 * (k + 1) + 1) s =
      (s ^ (1 : ℝ))⁻¹ *
        ∫ t in recursionLower 2 s (2 * (k + 1) + 1)..
            (2 + (2 * (k + 1) + 1 : ℕ)),
          ((t - 1) ^ (1 : ℝ))⁻¹ *
            ∫ v in recursionLower 2 (t - 1) (2 * k + 2)..
                (2 + (2 * k + 2 : ℕ)),
              suzukiLayer 1 2 (2 * k + 1) (v - 1) := by
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
    suzukiLayer_succ_succ]
  simp only [Real.rpow_one, dPowDensity, sub_self, Real.rpow_zero,
    mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  apply congrArg (fun z => s⁻¹ * z)
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega]
  rw [suzukiLayer_succ_succ 1 2 (t - 1) (2 * k)]
  simp only [Real.rpow_one, dPowDensity, sub_self, Real.rpow_zero,
    mul_one, Nat.cast_mul]
  norm_num

private theorem compact_tail_integral
    {f : ℝ → ℝ} {x B : ℝ}
    (hcont : ContinuousOn f (Icc x B))
    (hzero : ∀ t, B ≤ t → f t = 0) :
    IntegrableOn f (Ioi x) ∧
      (∫ t in Ioi x, f t) = ∫ t in min x B..B, f t := by
  exact MathlibNt.SieveTheory.compact_tail_integral hcont hzero

private theorem sourceIntegral_succ_eq_of_div_three_le_upper
    (k : ℕ) {s b c : ℝ} (_hs : 0 ≤ s)
    (hb : s / 3 ≤ b) (hc : s / 3 ≤ c) :
    upperRosserBoundarySourceIntegral (k + 1) s b =
      upperRosserBoundarySourceIntegral (k + 1) s c := by
  unfold upperRosserBoundarySourceIntegral
  have restrict (d : ℝ) (hd : s / 3 ≤ d) :
      (∫ a in Ioo 0 d,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMassAux (k + 1) s a d) =
      ∫ a in Ioo 0 (s / 3),
        a⁻¹ * a⁻¹ * upperRosserBoundaryMassAux (k + 1) s a d := by
    apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioo
    · intro a ha
      exact ⟨ha.1, ha.2.trans_le hd⟩
    · intro a ha
      have hsa : s / 3 ≤ a := by
        exact le_of_not_gt fun hlt => ha.2 ⟨ha.1.1, hlt⟩
      rw [upperRosserBoundaryMassAux_succ_eq_zero_of_div_three_le k hsa]
      simp
  rw [restrict b hb, restrict c hc]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro a ha
  dsimp only
  congr 1
  rw [upperRosserBoundaryMassAux_succ, upperRosserBoundaryMassAux_succ,
    min_eq_right hb, min_eq_right hc]

private theorem shifted_odd_suzukiLayer_continuousOn
    (k : ℕ) {x B : ℝ} (hx : 2 < x) :
    ContinuousOn (fun v => suzukiLayer 1 2 (2 * k + 1) (v - 1)) (Icc x B) := by
  apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num : (1 : ℝ) < 2)
    (2 * k + 1)).comp (continuous_id.sub continuous_const).continuousOn
  intro v hv
  unfold suzukiParityDomainOne KappaOneModel.parityDomain
  split <;> simp_all; linarith

private theorem weighted_suzukiLayer_odd_lowStrip
    (k : ℕ) {x : ℝ} (hx0 : 0 < x) (hx3 : x ≤ 3) :
    x * suzukiLayer 1 2 (2 * k + 3) x =
      3 * suzukiLayer 1 2 (2 * k + 3) 3 := by
  have hn : 3 ≤ 2 * k + 3 := by omega
  have hodd : (2 * k + 3) % 2 = 1 := by omega
  have hlowerx : recursionLower 2 x (2 * k + 3) = 3 := by
    unfold recursionLower sourceEpsilon
    rw [hodd]
    norm_num
    rw [max_eq_right hx3]
    apply min_eq_left
    have hnR : (3 : ℝ) ≤ 2 * k + 3 := by exact_mod_cast hn
    linarith
  have hlower3 : recursionLower 2 3 (2 * k + 3) = 3 := by
    unfold recursionLower sourceEpsilon
    rw [hodd]
    norm_num
    have hnR : (3 : ℝ) ≤ 2 * k + 3 := by exact_mod_cast hn
    linarith
  have hnum : suzukiLayerNumerator 1 2 (2 * k + 3) x =
      suzukiLayerNumerator 1 2 (2 * k + 3) 3 := by
    rw [show 2 * k + 3 = (2 * k + 1) + 2 by omega,
      suzukiLayerNumerator_succ_succ,
      suzukiLayerNumerator_succ_succ, hlowerx, hlower3]
  rw [suzukiLayer_eq_inv_rpow_mul_numerator,
    suzukiLayer_eq_inv_rpow_mul_numerator,
    show x ^ (1 : ℝ) = x by norm_num,
    show (3 : ℝ) ^ (1 : ℝ) = 3 by norm_num,
    ← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul,
    ← mul_assoc]
  norm_num [hnum]

private theorem shifted_even_suzukiLayer_continuousOn
    (k : ℕ) {x B : ℝ} (hx : 3 ≤ x) :
    ContinuousOn (fun t => suzukiLayer 1 2 (2 * k + 2) (t - 1)) (Icc x B) := by
  apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num : (1 : ℝ) < 2)
    (2 * k + 2)).comp (continuous_id.sub continuous_const).continuousOn
  intro t ht
  unfold suzukiParityDomainOne KappaOneModel.parityDomain
  split <;> simp_all; linarith

private theorem predecessor_source_tail_eq_interval
    (k : ℕ)
    (hid : ∀ x : ℝ, 1 < x →
      upperRosserBoundarySourceIntegral k x 1 =
        suzukiLayer 1 2 (2 * k + 1) x)
    {t : ℝ} (ht : 3 < t) :
    (∫ v in Ioi (t - 1),
      upperRosserBoundarySourceIntegral k (v - 1) 1) =
      ∫ v in recursionLower 2 (t - 1) (2 * k + 2)..
          (2 + (2 * k + 2 : ℕ)),
        suzukiLayer 1 2 (2 * k + 1) (v - 1) := by
  let B : ℝ := 2 + (2 * k + 2 : ℕ)
  let f : ℝ → ℝ := fun v =>
    upperRosserBoundarySourceIntegral k (v - 1) 1
  let g : ℝ → ℝ := fun v => suzukiLayer 1 2 (2 * k + 1) (v - 1)
  have hfg : ∀ v, 2 < v → f v = g v := by
    intro v hv
    exact hid (v - 1) (by linarith)
  have hgcont : ContinuousOn g (Icc (t - 1) B) :=
    shifted_odd_suzukiLayer_continuousOn k (by linarith)
  have hgzero : ∀ v, B ≤ v → g v = 0 := by
    intro v hv
    apply suzukiLayer_eq_zero_of_le
    dsimp [B, g] at hv ⊢
    push_cast at hv ⊢
    linarith
  have htail := compact_tail_integral hgcont hgzero
  have hmin : min (t - 1) B = recursionLower 2 (t - 1) (2 * k + 2) := by
    unfold recursionLower sourceEpsilon
    have heven : (2 * k + 2) % 2 = 0 := by omega
    rw [heven]
    norm_num
    rw [max_eq_left (by linarith : (2 : ℝ) ≤ t - 1)]
    dsimp [B]
    push_cast
    rfl
  change (∫ v in Ioi (t - 1), f v) = _
  calc
    (∫ v in Ioi (t - 1), f v) = ∫ v in Ioi (t - 1), g v := by
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards with v
      intro hv
      change t - 1 < v at hv
      exact hfg v (by linarith)
    _ = ∫ v in min (t - 1) B..B, g v := htail.2
    _ = _ := by
      rw [hmin]

private theorem tail_alignment_of_predecessor_identity
    (k : ℕ)
    (hid : ∀ x : ℝ, 1 < x →
      upperRosserBoundarySourceIntegral k x 1 =
        suzukiLayer 1 2 (2 * k + 1) x)
    (s : ℝ) :
    (∫ t in Ioi (recursionLower 2 s (2 * (k + 1) + 1)),
      (t - 1)⁻¹ * ∫ v in Ioi (t - 1),
        upperRosserBoundarySourceIntegral k (v - 1) 1) =
      ∫ t in recursionLower 2 s (2 * (k + 1) + 1)..
          (2 + (2 * (k + 1) + 1 : ℕ)),
        ((t - 1) ^ (1 : ℝ))⁻¹ *
          ∫ v in recursionLower 2 (t - 1) (2 * k + 2)..
              (2 + (2 * k + 2 : ℕ)),
            suzukiLayer 1 2 (2 * k + 1) (v - 1) := by
  let A : ℝ := recursionLower 2 s (2 * (k + 1) + 1)
  let B : ℝ := 2 + (2 * (k + 1) + 1 : ℕ)
  let F : ℝ → ℝ := fun t => (t - 1)⁻¹ *
    ∫ v in Ioi (t - 1), upperRosserBoundarySourceIntegral k (v - 1) 1
  let G : ℝ → ℝ := fun t => suzukiLayer 1 2 (2 * k + 2) (t - 1)
  have hA3 : 3 ≤ A := by
    dsimp [A]
    unfold recursionLower sourceEpsilon
    have hodd : (2 * (k + 1) + 1) % 2 = 1 := by omega
    rw [hodd]
    norm_num
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hFG : ∀ t, A < t → F t = G t := by
    intro t ht
    have ht3 : 3 < t := lt_of_le_of_lt hA3 ht
    rw [show F t = (t - 1)⁻¹ *
      ∫ v in Ioi (t - 1), upperRosserBoundarySourceIntegral k (v - 1) 1 by rfl,
      predecessor_source_tail_eq_interval k hid ht3]
    dsimp only [G]
    rw [show 2 * k + 2 = 2 * k + 2 by rfl]
    rw [suzukiLayer_succ_succ 1 2 (t - 1) (2 * k)]
    simp only [Real.rpow_one, dPowDensity, sub_self, Real.rpow_zero,
      mul_one, Nat.cast_mul]
    norm_num
  have hGcont : ContinuousOn G (Icc A B) :=
    shifted_even_suzukiLayer_continuousOn k hA3
  have hGzero : ∀ t, B ≤ t → G t = 0 := by
    intro t ht
    apply suzukiLayer_eq_zero_of_le
    dsimp [B, G] at ht ⊢
    push_cast at ht ⊢
    linarith
  have htail := compact_tail_integral hGcont hGzero
  have hAB : A ≤ B := by
    dsimp [A, B]
    unfold recursionLower
    exact min_le_right _ _
  change (∫ t in Ioi A, F t) = _
  calc
    (∫ t in Ioi A, F t) = ∫ t in Ioi A, G t := by
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards with t
      intro ht
      exact hFG t ht
    _ = ∫ t in A..B, G t := by simpa [min_eq_left hAB] using htail.2
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t
      intro ht
      rw [Set.uIoc_of_le hAB] at ht
      have ht3 : 3 < t := lt_of_le_of_lt hA3 ht.1
      rw [← hFG t ht.1]
      dsimp only [F]
      rw [predecessor_source_tail_eq_interval k hid ht3]
      simp only [Real.rpow_one]


private theorem upperRosserBoundaryMassAux_eq_zero_of_linear_support
    (k : ℕ) {s a b : ℝ} (hab : a ≤ b)
    (h : 2 * a + (2 * k + 1 : ℕ) * b ≤ s) :
    upperRosserBoundaryMassAux k s a b = 0 := by
  induction k generalizing s a b with
  | zero =>
      rw [upperRosserBoundaryMassAux_zero]
      rw [if_neg]
      intro hsupp
      norm_num at h
      nlinarith [hsupp.2, hsupp.1, hab]
  | succ k ih =>
      rw [upperRosserBoundaryMassAux_succ]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
      have hinner : (∫ x₁ in Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
        have hb0 : x₀ < b := hx₀.2.trans_le (min_le_left _ _)
        have hsupp : 2 * a + (2 * k + 1 : ℕ) * x₁ ≤ s - x₀ - x₁ := by
          push_cast at h ⊢
          have hx₁b : x₁ < b := hx₁.2.trans hb0
          nlinarith
        rw [ih hx₁.1.le hsupp]
        simp
      rw [hinner]
      simp

private theorem upperRosserBoundarySourceIntegral_eq_zero_of_linear_support
    (k : ℕ) {s : ℝ} (h : 2 + (2 * k + 1 : ℕ) ≤ s) :
    upperRosserBoundarySourceIntegral k s 1 = 0 := by
  unfold upperRosserBoundarySourceIntegral
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  rw [upperRosserBoundaryMassAux_eq_zero_of_linear_support k ha.2.le (by
    push_cast at h ⊢
    nlinarith [ha.2])]
  simp

private theorem weighted_sourceIntegral_succ_lowStrip
    (k : ℕ) {x : ℝ} (hx0 : 0 < x) (hx3 : x ≤ 3) :
    x * upperRosserBoundarySourceIntegral (k + 1) x 1 =
      3 * upperRosserBoundarySourceIntegral (k + 1) 3 1 := by
  have hxdiv : x / 3 ≤ (1 : ℝ) := by linarith
  rw [sourceIntegral_succ_eq_of_div_three_le_upper k hx0.le hxdiv le_rfl]
  have hhom := upperRosserBoundarySourceIntegral_homogeneous
    (k + 1) (c := x / 3) (s := 3) (b := 1) (by positivity)
  norm_num at hhom
  rw [← upperRosserBoundarySourceIntegral_one] at hhom
  rw [hhom]
  field_simp [hx0.ne']

private theorem source_succ_kernel_shape_of_support
    (k : ℕ) {s : ℝ} (hs : 3 / 2 ≤ s)
    (hssupp : s ≤ 2 + (2 * (k + 1) + 1 : ℕ)) :
    upperRosserBoundarySourceIntegral (k + 1) s 1 =
      s⁻¹ * ∫ t in Ioi (recursionLower 2 s (2 * (k + 1) + 1)),
        (t - 1)⁻¹ * ∫ v in Ioi (t - 1),
          upperRosserBoundarySourceIntegral k (v - 1) 1 := by
  rw [upperRosserBoundarySourceIntegral_succ_second_change_variables k hs,
    recursion_endpoint k hs hssupp]

private theorem source_succ_eq_layer_of_predecessor
    (k : ℕ)
    (hid : ∀ x : ℝ, 0 < x →
      upperRosserBoundarySourceIntegral k x 1 =
        suzukiLayer 1 2 (2 * k + 1) x)
    {s : ℝ} (hs : 3 / 2 ≤ s)
    (hssupp : s ≤ 2 + (2 * (k + 1) + 1 : ℕ)) :
    upperRosserBoundarySourceIntegral (k + 1) s 1 =
      suzukiLayer 1 2 (2 * (k + 1) + 1) s := by
  rw [source_succ_kernel_shape_of_support k hs hssupp,
    suzukiLayer_one_two_odd_succ_two_step_kernel]
  rw [tail_alignment_of_predecessor_identity k
    (fun x hx => hid x (by linarith)) s]
  simp only [Real.rpow_one]

private theorem source_layer_identity_all
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    upperRosserBoundarySourceIntegral k s 1 =
      suzukiLayer 1 2 (2 * k + 1) s := by
  induction k generalizing s with
  | zero =>
      rw [upperRosserBoundarySourceIntegral_one]
      exact upperRosserBoundarySourceLayerIdentity_zero hs
  | succ k ih =>
      by_cases hs3 : s ≤ 3
      · have hsrc := weighted_sourceIntegral_succ_lowStrip k hs hs3
        have hlay := weighted_suzukiLayer_odd_lowStrip k hs hs3
        have hlay' : s * suzukiLayer 1 2 (2 * (k + 1) + 1) s =
            3 * suzukiLayer 1 2 (2 * (k + 1) + 1) 3 := by
          simpa [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using hlay
        have hid3 := source_succ_eq_layer_of_predecessor k ih
          (s := 3) (by norm_num) (by
            norm_num [Nat.cast_add, Nat.cast_mul]
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith)
        nlinarith [hlay']
      · have h3s : 3 < s := lt_of_not_ge hs3
        by_cases hsupp : s ≤ 2 + (2 * (k + 1) + 1 : ℕ)
        · exact source_succ_eq_layer_of_predecessor k ih (by linarith) hsupp
        · have hsupp' : 2 + (2 * (k + 1) + 1 : ℕ) ≤ s := le_of_not_ge hsupp
          rw [upperRosserBoundarySourceIntegral_eq_zero_of_linear_support (k + 1) (by
            push_cast at hsupp' ⊢
            exact hsupp')]
          apply Eq.symm
          apply suzukiLayer_eq_zero_of_le
          exact hsupp'

/-- Exact residual after both nonlinear substitutions.  It contains only the two
support truncations and the predecessor source/layer identification; all
Jacobians, endpoints, and Suzuki recursion algebra have already been fixed. -/
def UpperRosserBoundarySourceSuccTailAlignment : Prop :=
  ∀ (k : ℕ) (s : ℝ), 3 / 2 ≤ s → s ≤ 4 →
    (∫ t in Set.Ioi (recursionLower 2 s (2 * (k + 1) + 1)),
      (t - 1)⁻¹ * ∫ v in Set.Ioi (t - 1),
        upperRosserBoundarySourceIntegral k (v - 1) 1) =
      ∫ t in recursionLower 2 s (2 * (k + 1) + 1)..
          (2 + (2 * (k + 1) + 1 : ℕ)),
        ((t - 1) ^ (1 : ℝ))⁻¹ *
          ∫ v in recursionLower 2 (t - 1) (2 * k + 2)..
              (2 + (2 * k + 2 : ℕ)),
            suzukiLayer 1 2 (2 * k + 1) (v - 1)

/-- The strongest exact assembler at the current boundary: the literal tail
alignment above closes the requested successor-layer identity with no sieve or
density hypothesis. -/
theorem suzukiUpperRosserBoundarySourceSuccLayerIdentity_of_tail_alignment
    (h : UpperRosserBoundarySourceSuccTailAlignment) :
    SuzukiUpperRosserBoundarySourceSuccLayerIdentity := by
  intro k s hs hshi
  rw [← upperRosserBoundarySourceIntegral_one]
  rw [upperRosserBoundarySourceIntegral_succ_two_suzuki_kernel_shape k hs hshi,
    suzukiLayer_one_two_odd_succ_two_step_kernel]
  rw [h k s hs hshi]
  simp only [Real.rpow_one]

/-- The tail alignment is unconditional.  The predecessor identity used under
both improper integrals is supplied by the global positive-source induction;
the open lower endpoints are handled only almost everywhere. -/
theorem upperRosserBoundarySourceSuccTailAlignment :
    UpperRosserBoundarySourceSuccTailAlignment := by
  intro k s _hs _hshi
  exact tail_alignment_of_predecessor_identity k
    (fun x hx => source_layer_identity_all k x (by linarith)) s

/-- Unconditional successor-layer identity. -/
theorem suzukiUpperRosserBoundarySourceSuccLayerIdentity :
    SuzukiUpperRosserBoundarySourceSuccLayerIdentity :=
  suzukiUpperRosserBoundarySourceSuccLayerIdentity_of_tail_alignment
    upperRosserBoundarySourceSuccTailAlignment

end

end MathlibNt.SieveTheory.LinearSieve
