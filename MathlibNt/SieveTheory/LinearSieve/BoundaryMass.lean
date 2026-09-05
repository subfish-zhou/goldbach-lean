import MathlibNt.SieveTheory.LinearSieve.RosserChains

/-!
# Continuous upper Rosser boundary mass

Recursive boundary mass, measurability, the depth-two logarithmic kernel,
Lipschitz estimates, and nonnegativity.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-- The continuous mass of depth-`2k` upper Rosser boundary chains.  The
additional argument `b` is the inherited strict upper bound for the largest
remaining coordinate; retaining it makes pair removal exactly recursive. -/
noncomputable def upperRosserBoundaryMassAux : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, s, a, _ => if 0 ≤ s ∧ s < 3 * a then 1 else 0
  | k + 1, s, a, b =>
      ∫ x₀ in Set.Ioo a (min b (s / 3)),
        x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁

/-- The continuous depth-`2k` boundary mass with the global logarithmic cutoff
`1`. -/
noncomputable def upperRosserBoundaryMass (k : ℕ) (s a : ℝ) : ℝ :=
  upperRosserBoundaryMassAux k s a 1

@[simp]
theorem upperRosserBoundaryMassAux_zero (s a b : ℝ) :
    upperRosserBoundaryMassAux 0 s a b =
      if 0 ≤ s ∧ s < 3 * a then 1 else 0 :=
  rfl

/-- The depth-zero residual mass is continuous in its level away from its two
affine boundary values. -/
theorem continuousAt_upperRosserBoundaryMassAux_zero_level
    {s a b : ℝ} (hs0 : s ≠ 0) (hs3 : s ≠ 3 * a) :
    ContinuousAt (fun t => upperRosserBoundaryMassAux 0 t a b) s := by
  by_cases h : 0 ≤ s ∧ s < 3 * a
  · have hspos : 0 < s := lt_of_le_of_ne h.1 (Ne.symm hs0)
    apply (show (fun t => upperRosserBoundaryMassAux 0 t a b) =ᶠ[nhds s]
      (fun _ => (1 : ℝ)) by
        filter_upwards [lt_mem_nhds hspos, eventually_lt_nhds h.2] with t ht0 ht3
        simp [upperRosserBoundaryMassAux_zero, ht0.le, ht3]).continuousAt
  · by_cases hsneg : s < 0
    · apply (show (fun t => upperRosserBoundaryMassAux 0 t a b) =ᶠ[nhds s]
        (fun _ => (0 : ℝ)) by
          filter_upwards [eventually_lt_nhds hsneg] with t ht
          simp [upperRosserBoundaryMassAux_zero, not_le.mpr ht]).continuousAt
    · have hsnonneg : 0 ≤ s := le_of_not_gt hsneg
      have h3le : 3 * a ≤ s := by
        by_contra hnot
        exact h ⟨hsnonneg, lt_of_not_ge hnot⟩
      have h3lt : 3 * a < s := lt_of_le_of_ne h3le (Ne.symm hs3)
      apply (show (fun t => upperRosserBoundaryMassAux 0 t a b) =ᶠ[nhds s]
        (fun _ => (0 : ℝ)) by
          filter_upwards [lt_mem_nhds h3lt] with t ht
          simp [upperRosserBoundaryMassAux_zero, not_lt.mpr ht.le]).continuousAt

/-- The depth-zero residual mass is jointly continuous in its level and lower
cutoff away from the two affine jump hypersurfaces.  The inherited upper cutoff
does not occur at depth zero. -/
theorem continuousAt_upperRosserBoundaryMassAux_zero_level_lower
    {s a b : ℝ} (hs0 : s ≠ 0) (hs3 : s ≠ 3 * a) :
    ContinuousAt
      (fun p : ℝ × ℝ => upperRosserBoundaryMassAux 0 p.1 p.2 b) (s, a) := by
  have hlevel : ContinuousAt (fun p : ℝ × ℝ => p.1) (s, a) := by fun_prop
  have hterminal :
      ContinuousAt (fun p : ℝ × ℝ => p.1 - 3 * p.2) (s, a) := by fun_prop
  by_cases h : 0 ≤ s ∧ s < 3 * a
  · have hspos : 0 < s := lt_of_le_of_ne h.1 (Ne.symm hs0)
    have heventuallyPos :
        ∀ᶠ p : ℝ × ℝ in nhds (s, a), 0 < p.1 :=
      hlevel (Ioi_mem_nhds hspos)
    have hdiff : s - 3 * a < 0 := sub_neg.mpr h.2
    have heventuallyTerminal :
        ∀ᶠ p : ℝ × ℝ in nhds (s, a), p.1 - 3 * p.2 < 0 :=
      hterminal (Iio_mem_nhds hdiff)
    apply (show (fun p : ℝ × ℝ =>
        upperRosserBoundaryMassAux 0 p.1 p.2 b) =ᶠ[nhds (s, a)]
          (fun _ => (1 : ℝ)) by
      filter_upwards [heventuallyPos, heventuallyTerminal] with p hp hpt
      simp [upperRosserBoundaryMassAux_zero, hp.le, sub_neg.mp hpt]).continuousAt
  · by_cases hsneg : s < 0
    · have heventuallyNeg :
          ∀ᶠ p : ℝ × ℝ in nhds (s, a), p.1 < 0 :=
        hlevel (Iio_mem_nhds hsneg)
      apply (show (fun p : ℝ × ℝ =>
          upperRosserBoundaryMassAux 0 p.1 p.2 b) =ᶠ[nhds (s, a)]
            (fun _ => (0 : ℝ)) by
        filter_upwards [heventuallyNeg] with p hp
        simp [upperRosserBoundaryMassAux_zero, not_le.mpr hp]).continuousAt
    · have hsnonneg : 0 ≤ s := le_of_not_gt hsneg
      have h3le : 3 * a ≤ s := by
        by_contra hnot
        exact h ⟨hsnonneg, lt_of_not_ge hnot⟩
      have hdiff : 0 < s - 3 * a := sub_pos.mpr
        (lt_of_le_of_ne h3le (Ne.symm hs3))
      have heventuallyTerminal :
          ∀ᶠ p : ℝ × ℝ in nhds (s, a), 0 < p.1 - 3 * p.2 :=
        hterminal (Ioi_mem_nhds hdiff)
      apply (show (fun p : ℝ × ℝ =>
          upperRosserBoundaryMassAux 0 p.1 p.2 b) =ᶠ[nhds (s, a)]
            (fun _ => (0 : ℝ)) by
        filter_upwards [heventuallyTerminal] with p hp
        simp [upperRosserBoundaryMassAux_zero, not_lt.mpr (sub_nonneg.mp hp.le)]).continuousAt

/-- Affine specialization of the joint depth-zero continuity statement used in
the inner dominated-convergence step of the recursive Rosser mass. -/
theorem continuousAt_upperRosserBoundaryMassAux_zero_affine_level_lower
    {s a x₀ x₁ b : ℝ} (hzero : s - x₀ - x₁ ≠ 0)
    (hterminal : s - x₀ - x₁ ≠ 3 * a) :
    ContinuousAt (fun p : ℝ × ℝ =>
      upperRosserBoundaryMassAux 0 (p.1 - x₀ - x₁) p.2 b) (s, a) := by
  have hmap : ContinuousAt
      (fun p : ℝ × ℝ => (p.1 - x₀ - x₁, p.2)) (s, a) := by fun_prop
  have hcomp : ContinuousAt
      ((fun q : ℝ × ℝ => upperRosserBoundaryMassAux 0 q.1 q.2 b) ∘
        (fun p : ℝ × ℝ => (p.1 - x₀ - x₁, p.2))) (s, a) :=
    ContinuousAt.comp
      (continuousAt_upperRosserBoundaryMassAux_zero_level_lower
        (b := b) hzero hterminal) hmap
  simpa [Function.comp_def] using hcomp

/-- On a cell in the peeled coordinate, the depth-zero residual is bounded by
its left-endpoint value except on the unique cell meeting the affine boundary
`x = s - x₀ - 3a`.  The other depth-zero jump is downward in this orientation
and therefore costs nothing in an upper majorant. -/
theorem upperRosserBoundaryMassAux_zero_residual_le_left_add_boundary
    {s x₀ a l r x : ℝ} (hlx : l ≤ x) (hxr : x ≤ r) :
    upperRosserBoundaryMassAux 0 (s - x₀ - x) a x ≤
      upperRosserBoundaryMassAux 0 (s - x₀ - l) a l +
        if s - x₀ - 3 * a ∈ Set.Icc l r then 1 else 0 := by
  rw [upperRosserBoundaryMassAux_zero, upperRosserBoundaryMassAux_zero]
  by_cases hx : 0 ≤ s - x₀ - x ∧ s - x₀ - x < 3 * a
  · rw [if_pos hx]
    by_cases hboundary : s - x₀ - 3 * a ∈ Set.Icc l r
    · rw [if_pos hboundary]
      split_ifs <;> norm_num
    · rw [if_neg hboundary]
      have hlower : 0 ≤ s - x₀ - l := by linarith [hx.1]
      have hupper : s - x₀ - l < 3 * a := by
        by_contra hnot
        apply hboundary
        constructor
        · linarith
        · linarith [hx.2]
      rw [if_pos ⟨hlower, hupper⟩]
      norm_num
  · rw [if_neg hx]
    positivity

/-- A nonzero depth-zero residual below a peeled Rosser pair retains the
depth-two lower support for the outer coordinate.  This remains valid for the
continuous majorant, independently of whether the pair comes from an exact
boundary chain. -/
theorem upperRosserBoundaryMassAux_zero_ne_zero_outer_lower
    {s a x₀ x₁ : ℝ} (hs : 3 / 2 ≤ s) (hx₀ : x₀ ≤ s / 3)
    (hx₁ : x₁ < x₀)
    (h : upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁ ≠ 0) :
    1 / 6 < a := by
  rw [upperRosserBoundaryMassAux_zero] at h
  split at h
  · rename_i hres
    nlinarith [hres.2]
  · simp at h

theorem upperRosserBoundaryMassAux_succ (k : ℕ) (s a b : ℝ) :
    upperRosserBoundaryMassAux (k + 1) s a b =
      ∫ x₀ in Set.Ioo a (min b (s / 3)),
        x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁ :=
  rfl

@[simp]
theorem upperRosserBoundaryMass_zero (s a : ℝ) :
    upperRosserBoundaryMass 0 s a =
      if 0 ≤ s ∧ s < 3 * a then 1 else 0 :=
  rfl

theorem upperRosserBoundaryMass_succ (k : ℕ) (s a : ℝ) :
    upperRosserBoundaryMass (k + 1) s a =
      ∫ x₀ in Set.Ioo a (min 1 (s / 3)),
        x₀⁻¹ * ∫ x₁ in Set.Ioo a x₀,
          x₁⁻¹ * upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁ :=
  rfl

/-- The finite-depth Rosser boundary mass is jointly strongly measurable in its
level, lower cutoff, and inherited upper cutoff. -/
theorem stronglyMeasurable_upperRosserBoundaryMassAux (k : ℕ) :
    MeasureTheory.StronglyMeasurable
      (fun p : (ℝ × ℝ) × ℝ =>
        upperRosserBoundaryMassAux k p.1.1 p.1.2 p.2) := by
  induction k with
  | zero =>
      simp only [upperRosserBoundaryMassAux_zero]
      apply Measurable.stronglyMeasurable
      apply Measurable.ite
      · exact (measurableSet_le measurable_const
          (measurable_fst.comp measurable_fst)).inter
          (measurableSet_lt (measurable_fst.comp measurable_fst)
            (measurable_const.mul (measurable_snd.comp measurable_fst)))
      · exact measurable_const
      · exact measurable_const
  | succ k ih =>
      rw [show (fun p : (ℝ × ℝ) × ℝ =>
          upperRosserBoundaryMassAux (k + 1) p.1.1 p.1.2 p.2) =
          fun p => ∫ x₀ in Set.Ioo p.1.2 (min p.2 (p.1.1 / 3)),
            x₀⁻¹ * ∫ x₁ in Set.Ioo p.1.2 x₀,
              x₁⁻¹ * upperRosserBoundaryMassAux k
                (p.1.1 - x₀ - x₁) p.1.2 x₁ by
        funext p
        exact upperRosserBoundaryMassAux_succ k p.1.1 p.1.2 p.2]
      let innerSet : Set (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ)) :=
        {r | r.1.1.1.2 < r.2 ∧ r.2 < r.1.2}
      let innerIntegrand : (((ℝ × ℝ) × ℝ) × ℝ) × ℝ → ℝ := fun r =>
        innerSet.indicator (fun r => r.2⁻¹ * upperRosserBoundaryMassAux k
          (r.1.1.1.1 - r.1.2 - r.2) r.1.1.1.2 r.2) r
      have hmap : Measurable (fun r : (((ℝ × ℝ) × ℝ) × ℝ) × ℝ =>
          ((r.1.1.1.1 - r.1.2 - r.2, r.1.1.1.2), r.2)) := by
        fun_prop
      have hinnerSet : MeasurableSet innerSet := by
        apply (measurableSet_lt
          (measurable_snd.comp
            (measurable_fst.comp (measurable_fst.comp measurable_fst)))
          measurable_snd).inter
        exact measurableSet_lt measurable_snd
          (measurable_snd.comp measurable_fst)
      have hinnerIntegrand :
          MeasureTheory.StronglyMeasurable innerIntegrand := by
        apply MeasureTheory.StronglyMeasurable.indicator
        · exact measurable_snd.inv.stronglyMeasurable.mul
            (ih.comp_measurable hmap)
        · exact hinnerSet
      have hinnerRaw :=
        hinnerIntegrand.integral_prod_right' (ν := MeasureTheory.volume)
      have hinner : MeasureTheory.StronglyMeasurable
          (fun r : ((ℝ × ℝ) × ℝ) × ℝ =>
            ∫ x₁ in Set.Ioo r.1.1.2 r.2,
              x₁⁻¹ * upperRosserBoundaryMassAux k
                (r.1.1.1 - r.2 - x₁) r.1.1.2 x₁) := by
        convert hinnerRaw using 1
        funext r
        rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
        rfl
      let outerSet : Set ((((ℝ × ℝ) × ℝ) × ℝ)) :=
        {r | r.1.1.2 < r.2 ∧ r.2 < min r.1.2 (r.1.1.1 / 3)}
      let outerIntegrand : (((ℝ × ℝ) × ℝ) × ℝ) → ℝ := fun r =>
        outerSet.indicator (fun r => r.2⁻¹ *
          (∫ x₁ in Set.Ioo r.1.1.2 r.2,
            x₁⁻¹ * upperRosserBoundaryMassAux k
              (r.1.1.1 - r.2 - x₁) r.1.1.2 x₁)) r
      have houterSet : MeasurableSet outerSet := by
        apply (measurableSet_lt
          (measurable_snd.comp (measurable_fst.comp measurable_fst))
          measurable_snd).inter
        exact measurableSet_lt measurable_snd
          ((measurable_snd.comp measurable_fst).min
            ((measurable_fst.comp
              (measurable_fst.comp measurable_fst)).div_const 3))
      have houterIntegrand :
          MeasureTheory.StronglyMeasurable outerIntegrand := by
        apply MeasureTheory.StronglyMeasurable.indicator
        · exact measurable_snd.inv.stronglyMeasurable.mul hinner
        · exact houterSet
      have houterRaw :=
        houterIntegrand.integral_prod_right' (ν := MeasureTheory.volume)
      convert houterRaw using 1
      funext p
      rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
      rfl

/-- The inner integral appearing in the Rosser pair recursion is strongly
measurable jointly in the residual level, lower cutoff, and outer coordinate. -/
theorem stronglyMeasurable_integral_inv_mul_upperRosserBoundaryMassAux
    (k : ℕ) :
    MeasureTheory.StronglyMeasurable
      (fun r : (ℝ × ℝ) × ℝ =>
        ∫ x in Set.Ioo r.1.2 r.2,
          x⁻¹ * upperRosserBoundaryMassAux k
            (r.1.1 - r.2 - x) r.1.2 x) := by
  let innerSet : Set ((((ℝ × ℝ) × ℝ) × ℝ)) :=
    {r | r.1.1.2 < r.2 ∧ r.2 < r.1.2}
  let innerIntegrand : (((ℝ × ℝ) × ℝ) × ℝ) → ℝ := fun r =>
    innerSet.indicator (fun r => r.2⁻¹ * upperRosserBoundaryMassAux k
      (r.1.1.1 - r.1.2 - r.2) r.1.1.2 r.2) r
  have hmap : Measurable (fun r : (((ℝ × ℝ) × ℝ) × ℝ) =>
      ((r.1.1.1 - r.1.2 - r.2, r.1.1.2), r.2)) := by
    fun_prop
  have hinnerSet : MeasurableSet innerSet := by
    apply (measurableSet_lt
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
      measurable_snd).inter
    exact measurableSet_lt measurable_snd (measurable_snd.comp measurable_fst)
  have hinnerIntegrand :
      MeasureTheory.StronglyMeasurable innerIntegrand := by
    apply MeasureTheory.StronglyMeasurable.indicator
    · exact measurable_snd.inv.stronglyMeasurable.mul
        ((stronglyMeasurable_upperRosserBoundaryMassAux k).comp_measurable hmap)
    · exact hinnerSet
  have hinnerRaw :=
    hinnerIntegrand.integral_prod_right' (ν := MeasureTheory.volume)
  convert hinnerRaw using 1
  funext r
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
  rfl

/-- At depth zero, the residual factor is exactly the indicator of the moving
terminal shell in the peeled coordinate. -/
theorem inv_mul_upperRosserBoundaryMassAux_zero_eq_indicator
    (s a x₀ x₁ : ℝ) :
    x₁⁻¹ * upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁ =
      (Set.Ioc (s - x₀ - 3 * a) (s - x₀)).indicator (fun x => x⁻¹) x₁ := by
  rw [upperRosserBoundaryMassAux_zero]
  have hmem : x₁ ∈ Set.Ioc (s - x₀ - 3 * a) (s - x₀) ↔
      0 ≤ s - x₀ - x₁ ∧ s - x₀ - x₁ < 3 * a := by
    constructor <;> intro h
    · exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact ⟨by linarith [h.2], by linarith [h.1]⟩
  by_cases h : 0 ≤ s - x₀ - x₁ ∧ s - x₀ - x₁ < 3 * a
  · rw [if_pos h, Set.indicator_of_mem (hmem.mpr h), mul_one]
  · rw [if_neg h, Set.indicator_of_notMem (mt hmem.mp h), mul_zero]

/-- The depth-zero inner integrand is integrable whenever the fixed lower
endpoint is positive. -/
theorem integrableOn_inv_mul_upperRosserBoundaryMassAux_zero
    {s a x₀ : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun x₁ => x₁⁻¹ *
        upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁)
      (Set.Ioo a x₀) := by
  by_cases hax₀ : a < x₀
  · have hinvInterval : IntervalIntegrable (fun x : ℝ => x⁻¹)
        MeasureTheory.volume a x₀ := by
      apply intervalIntegral.intervalIntegrable_inv (f := fun x : ℝ => x)
      · intro x hx
        rw [Set.uIcc_of_le hax₀.le] at hx
        exact ne_of_gt (ha.trans_le hx.1)
      · exact continuous_id.continuousOn
    have hinv : MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹)
        (Set.Ioo a x₀) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hax₀.le).mp hinvInterval
    apply (hinv.indicator
      (show MeasurableSet (Set.Ioc (s - x₀ - 3 * a) (s - x₀)) from
        measurableSet_Ioc)).congr_fun ?_ measurableSet_Ioo
    intro x₁ _
    exact (inv_mul_upperRosserBoundaryMassAux_zero_eq_indicator
      s a x₀ x₁).symm
  · rw [Set.Ioo_eq_empty hax₀]
    exact MeasureTheory.integrableOn_empty

/-- Without any ordering assumptions, the depth-zero inner integral is the
reciprocal integral over its exact moving shell. -/
theorem integral_upperRosserBoundaryMassAux_zero_eq_integral_inter
    {s a x₀ : ℝ} :
    (∫ x₁ in Set.Ioo a x₀,
      x₁⁻¹ * upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁) =
      ∫ x₁ in Set.Ioo a x₀ ∩
        Set.Ioc (s - x₀ - 3 * a) (s - x₀), x₁⁻¹ := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    (g := fun x₁ =>
      (Set.Ioc (s - x₀ - 3 * a) (s - x₀)).indicator
        (fun x₁ => x₁⁻¹) x₁)]
  · rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  · intro x₁ _
    exact inv_mul_upperRosserBoundaryMassAux_zero_eq_indicator s a x₀ x₁

/-- On the outer Rosser range, the upper edge of the terminal shell is
automatic, leaving a reciprocal integral with one moving lower endpoint. -/
theorem integral_upperRosserBoundaryMassAux_zero_eq_integral_Ioo
    {s a x₀ : ℝ} (ha : 0 < a) (hx₀s : x₀ < s / 3) :
    (∫ x₁ in Set.Ioo a x₀,
      x₁⁻¹ * upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁) =
      ∫ x₁ in Set.Ioo (max a (s - x₀ - 3 * a)) x₀, x₁⁻¹ := by
  rw [integral_upperRosserBoundaryMassAux_zero_eq_integral_inter]
  have hset : Set.Ioo a x₀ ∩ Set.Ioc (s - x₀ - 3 * a) (s - x₀) =
      Set.Ioo (max a (s - x₀ - 3 * a)) x₀ := by
    ext x₁
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioc, max_lt_iff]
    constructor
    · rintro ⟨⟨hx₁a, hx₁x₀⟩, hlower, _⟩
      exact ⟨⟨hx₁a, hlower⟩, hx₁x₀⟩
    · rintro ⟨⟨hx₁a, hlower⟩, hx₁x₀⟩
      refine ⟨⟨hx₁a, hx₁x₀⟩, hlower, ?_⟩
      have hx₁pos : 0 < x₁ := ha.trans hx₁a
      have hx₀pos : 0 < x₀ := hx₁pos.trans hx₁x₀
      linarith
  rw [hset]

/-- Exact logarithmic evaluation of the depth-zero inner integral.  The
conditional records precisely whether the moving terminal shell is nonempty. -/
theorem integral_upperRosserBoundaryMassAux_zero_eq_log
    {s a x₀ : ℝ} (ha : 0 < a) (hx₀s : x₀ < s / 3) :
    (∫ x₁ in Set.Ioo a x₀,
      x₁⁻¹ * upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁) =
      if max a (s - x₀ - 3 * a) < x₀ then
        Real.log (x₀ / max a (s - x₀ - 3 * a)) else 0 := by
  rw [integral_upperRosserBoundaryMassAux_zero_eq_integral_Ioo ha hx₀s]
  by_cases hcell : max a (s - x₀ - 3 * a) < x₀
  · rw [if_pos hcell, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hcell.le, integral_inv_of_pos]
    · exact lt_of_lt_of_le ha (le_max_left _ _)
    · exact (lt_of_lt_of_le ha (le_max_left _ _)).trans hcell
  · rw [if_neg hcell]
    have hempty : Set.Ioo (max a (s - x₀ - 3 * a)) x₀ = ∅ :=
      Set.Ioo_eq_empty hcell
    rw [hempty, MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure]

/-- The first positive boundary depth is therefore an explicit one-dimensional
piecewise logarithmic integral. -/
theorem upperRosserBoundaryMass_one_eq_integral_log
    {s a : ℝ} (ha : 0 < a) :
    upperRosserBoundaryMass 1 s a =
      ∫ x₀ in Set.Ioo a (min 1 (s / 3)), x₀⁻¹ *
        if max a (s - x₀ - 3 * a) < x₀ then
          Real.log (x₀ / max a (s - x₀ - 3 * a)) else 0 := by
  rw [show upperRosserBoundaryMass 1 s a =
      upperRosserBoundaryMass (0 + 1) s a by norm_num,
    upperRosserBoundaryMass_succ]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro x₀ hx₀
  change x₀⁻¹ * (∫ x₁ in Set.Ioo a x₀,
      x₁⁻¹ * upperRosserBoundaryMassAux 0 (s - x₀ - x₁) a x₁) = _
  rw [integral_upperRosserBoundaryMassAux_zero_eq_log ha
    (hx₀.2.trans_le (min_le_right _ _))]

/-- The conditional logarithm left after evaluating the inner depth-two
boundary integral. -/
noncomputable def upperRosserBoundaryLogKernel (s a x₀ : ℝ) : ℝ :=
  if max a (s - x₀ - 3 * a) < x₀ then
    Real.log (x₀ / max a (s - x₀ - 3 * a)) else 0

/-- On the ordered region `a < x₀`, the depth-two logarithmic kernel has only
the two affine break loci `2x₀ = s - 3a` and `x₀ = s - 4a`. -/
theorem upperRosserBoundaryLogKernel_eq_piecewise
    {s a x₀ : ℝ} (hax₀ : a < x₀) :
    upperRosserBoundaryLogKernel s a x₀ =
      if (s - 3 * a) / 2 < x₀ then
        if s - 4 * a ≤ x₀ then Real.log (x₀ / a)
        else Real.log (x₀ / (s - x₀ - 3 * a))
      else 0 := by
  rw [upperRosserBoundaryLogKernel]
  by_cases hswitch : s - x₀ - 3 * a ≤ a
  · rw [max_eq_left hswitch]
    have hactive : (s - 3 * a) / 2 < x₀ := by linarith
    have hbranch : s - 4 * a ≤ x₀ := by linarith
    simp [hax₀, hactive, hbranch]
  · have hswitch' : a ≤ s - x₀ - 3 * a := le_of_not_ge hswitch
    rw [max_eq_right hswitch']
    by_cases hactive : s - x₀ - 3 * a < x₀
    · have hthreshold : (s - 3 * a) / 2 < x₀ := by linarith
      have hbranch : ¬s - 4 * a ≤ x₀ := by linarith
      simp [hactive, hthreshold, hbranch]
    · have hthreshold : ¬(s - 3 * a) / 2 < x₀ := by linarith
      simp [hactive, hthreshold]

/-- On the positive ordered region, the apparent piecewise kernel is simply the
positive part of one continuous logarithmic ratio.  Thus its internal affine
break loci create no jump discontinuities. -/
theorem upperRosserBoundaryLogKernel_eq_max_log_sub
    {s a x₀ : ℝ} (ha : 0 < a) (hax₀ : a ≤ x₀) :
    upperRosserBoundaryLogKernel s a x₀ =
      max 0 (Real.log x₀ - Real.log (max a (s - x₀ - 3 * a))) := by
  rw [upperRosserBoundaryLogKernel]
  have hx₀ : 0 < x₀ := ha.trans_le hax₀
  have hden : 0 < max a (s - x₀ - 3 * a) :=
    ha.trans_le (le_max_left _ _)
  by_cases hactive : max a (s - x₀ - 3 * a) < x₀
  · rw [if_pos hactive, Real.log_div hx₀.ne' hden.ne']
    symm
    exact max_eq_right
      (sub_nonneg.mpr (Real.log_le_log hden hactive.le))
  · rw [if_neg hactive]
    symm
    exact max_eq_left
      (sub_nonpos.mpr (Real.log_le_log hx₀ (le_of_not_gt hactive)))

/-- The logarithm is explicitly Lipschitz on the screened coordinate interval.
This controls the oscillation of each smooth branch of the depth-two kernel. -/
theorem abs_log_sub_log_le_six_of_one_sixth_le
    {x y : ℝ} (hx : 1 / 6 ≤ x) (hy : 1 / 6 ≤ y) :
    |Real.log x - Real.log y| ≤ 6 * |x - y| := by
  have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hx
  have hypos : 0 < y := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hy
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hxpos hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hlog : Real.log y - Real.log x ≤ 6 * (y - x) := by
      rw [← Real.log_div hypos.ne' hxpos.ne']
      calc
        Real.log (y / x) ≤ y / x - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
        _ = (y - x) / x := by field_simp
        _ ≤ 6 * (y - x) := by
          rw [div_le_iff₀ hxpos]
          nlinarith
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hypos hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [← Real.log_div hxpos.ne' hypos.ne']
    calc
      Real.log (x / y) ≤ x / y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
      _ = (x - y) / y := by field_simp
      _ ≤ 6 * (x - y) := by
        rw [div_le_iff₀ hypos]
        nlinarith

/-- Reciprocal coordinates are explicitly Lipschitz on the screened interval. -/
theorem abs_inv_sub_inv_le_thirty_six_of_one_sixth_le
    {x y : ℝ} (hx : 1 / 6 ≤ x) (hy : 1 / 6 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ 36 * |x - y| := by
  have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hx
  have hypos : 0 < y := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hy
  rw [inv_sub_inv hxpos.ne' hypos.ne', abs_div, abs_mul,
    abs_of_pos hxpos, abs_of_pos hypos]
  have hxy : 1 / 36 ≤ x * y := by nlinarith
  have hxypos : 0 < x * y := mul_pos hxpos hypos
  rw [div_le_iff₀ hxypos, abs_sub_comm]
  have habs : 0 ≤ |x - y| := abs_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hxy habs
  nlinarith

/-- Ratios of screened coordinates have an explicit logarithmic oscillation
bound.  This is the smooth-cell estimate for both branches of the depth-two
kernel. -/
theorem abs_log_div_sub_log_div_le_six_of_one_sixth_le
    {x a y b : ℝ}
    (hx : 1 / 6 ≤ x) (ha : 1 / 6 ≤ a)
    (hy : 1 / 6 ≤ y) (hb : 1 / 6 ≤ b) :
    |Real.log (x / a) - Real.log (y / b)| ≤
      6 * (|x - y| + |a - b|) := by
  have hx0 : x ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hx)
  have ha0 : a ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha)
  have hy0 : y ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hy)
  have hb0 : b ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hb)
  rw [Real.log_div hx0 ha0, Real.log_div hy0 hb0]
  calc
    |(Real.log x - Real.log a) - (Real.log y - Real.log b)| =
        |(Real.log x - Real.log y) - (Real.log a - Real.log b)| := by ring_nf
    _ ≤ |Real.log x - Real.log y| + |Real.log a - Real.log b| := abs_sub _ _
    _ ≤ 6 * |x - y| + 6 * |a - b| :=
      add_le_add (abs_log_sub_log_le_six_of_one_sixth_le hx hy)
        (abs_log_sub_log_le_six_of_one_sixth_le ha hb)
    _ = 6 * (|x - y| + |a - b|) := by ring

/-- The whole depth-two logarithmic kernel is uniformly Lipschitz on its
screened ordered domain.  In particular, the two affine branch loci in
`upperRosserBoundaryLogKernel_eq_piecewise` require no exceptional strips. -/
theorem abs_upperRosserBoundaryLogKernel_sub_le
    {s a x₀ t b y₀ : ℝ}
    (ha : 1 / 6 ≤ a) (hax₀ : a ≤ x₀)
    (hb : 1 / 6 ≤ b) (hby₀ : b ≤ y₀) :
    |upperRosserBoundaryLogKernel s a x₀ -
        upperRosserBoundaryLogKernel t b y₀| ≤
      6 * (2 * |x₀ - y₀| + |s - t| + 4 * |a - b|) := by
  have haPos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 6).trans_le ha
  have hbPos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hb
  rw [upperRosserBoundaryLogKernel_eq_max_log_sub haPos hax₀,
    upperRosserBoundaryLogKernel_eq_max_log_sub hbPos hby₀]
  let d := max a (s - x₀ - 3 * a)
  let e := max b (t - y₀ - 3 * b)
  have hd : 1 / 6 ≤ d := ha.trans (le_max_left _ _)
  have he : 1 / 6 ≤ e := hb.trans (le_max_left _ _)
  have hmax :
      |max 0 (Real.log x₀ - Real.log d) -
          max 0 (Real.log y₀ - Real.log e)| ≤
        |(Real.log x₀ - Real.log d) -
          (Real.log y₀ - Real.log e)| := by
    simpa [max_comm] using abs_max_sub_max_le_abs
      (Real.log x₀ - Real.log d) (Real.log y₀ - Real.log e) 0
  have hlogs :
      |(Real.log x₀ - Real.log d) -
          (Real.log y₀ - Real.log e)| ≤
        6 * (|x₀ - y₀| + |d - e|) := by
    calc
      |(Real.log x₀ - Real.log d) - (Real.log y₀ - Real.log e)| =
          |Real.log (x₀ / d) - Real.log (y₀ / e)| := by
            rw [Real.log_div
              (ne_of_gt (haPos.trans_le hax₀))
              (ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hd)),
              Real.log_div
              (ne_of_gt (hbPos.trans_le hby₀))
              (ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le he))]
      _ ≤ 6 * (|x₀ - y₀| + |d - e|) :=
        abs_log_div_sub_log_div_le_six_of_one_sixth_le
          (ha.trans hax₀) hd (hb.trans hby₀) he
  have hden :
      |d - e| ≤ |s - t| + |x₀ - y₀| + 4 * |a - b| := by
    dsimp [d, e]
    have h₁ := abs_max_sub_max_le_max a (s - x₀ - 3 * a)
      b (t - y₀ - 3 * b)
    have h₂ :
        max |a - b| |(s - x₀ - 3 * a) - (t - y₀ - 3 * b)| ≤
          |a - b| + |(s - x₀ - 3 * a) - (t - y₀ - 3 * b)| :=
      max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))
    have h₃ :
        |(s - x₀ - 3 * a) - (t - y₀ - 3 * b)| ≤
          |s - t| + |x₀ - y₀| + 3 * |a - b| := by
      calc
        |(s - x₀ - 3 * a) - (t - y₀ - 3 * b)| =
            |(s - t) + (-(x₀ - y₀)) + (-(3 * (a - b)))| := by
              congr 1
              ring
        _ ≤ |(s - t) + (-(x₀ - y₀))| + |-(3 * (a - b))| :=
          abs_add_le _ _
        _ ≤ (|s - t| + |-(x₀ - y₀)|) + |-(3 * (a - b))| := by
          gcongr
          exact abs_add_le _ _
        _ = |s - t| + |x₀ - y₀| + 3 * |a - b| := by
          rw [abs_neg, abs_neg, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    linarith
  calc
    |max 0 (Real.log x₀ - Real.log d) -
        max 0 (Real.log y₀ - Real.log e)| ≤
      |(Real.log x₀ - Real.log d) -
        (Real.log y₀ - Real.log e)| := hmax
    _ ≤ 6 * (|x₀ - y₀| + |d - e|) := hlogs
    _ ≤ 6 * (2 * |x₀ - y₀| + |s - t| + 4 * |a - b|) := by
      nlinarith

/-- The depth-two boundary mass expressed using its named logarithmic kernel. -/
theorem upperRosserBoundaryMass_one_eq_integral_logKernel
    {s a : ℝ} (ha : 0 < a) :
    upperRosserBoundaryMass 1 s a =
      ∫ x₀ in Set.Ioo a (min 1 (s / 3)),
        x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ := by
  simpa [upperRosserBoundaryLogKernel] using
    upperRosserBoundaryMass_one_eq_integral_log (s := s) ha

/-- The first positive residual boundary depth has the same logarithmic-kernel
description with an arbitrary inherited upper face. -/
theorem upperRosserBoundaryMassAux_one_eq_integral_logKernel
    {s a b : ℝ} (ha : 0 < a) :
    upperRosserBoundaryMassAux 1 s a b =
      ∫ x₀ in Set.Ioo a (min b (s / 3)),
        x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ := by
  change upperRosserBoundaryMassAux (0 + 1) s a b = _
  rw [upperRosserBoundaryMassAux_succ]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro x₀ hx₀
  simp only
  rw [integral_upperRosserBoundaryMassAux_zero_eq_log ha
    (hx₀.2.trans_le (min_le_right _ _))]
  rfl

/-- The conditional logarithmic kernel is nonnegative above a positive lower
cutoff. -/
theorem upperRosserBoundaryLogKernel_nonneg
    {s a x₀ : ℝ} (ha : 0 < a) :
    0 ≤ upperRosserBoundaryLogKernel s a x₀ := by
  rw [upperRosserBoundaryLogKernel]
  split_ifs with hcell
  · apply Real.log_nonneg
    apply (one_le_div₀ (ha.trans_le (le_max_left _ _))).2
    exact hcell.le
  · exact le_rfl

/-- Uniform bound for the explicit conditional logarithmic kernel on the
screened box `1 / 6 ≤ a`, `x₀ ≤ 1`.  It is independent of `s`, hence uniform
in particular for `3 / 2 ≤ s ≤ 4`. -/
theorem upperRosserBoundaryLogKernel_le_log_six
    {s a x₀ : ℝ} (ha : 1 / 6 ≤ a) (hx₀ : x₀ ≤ 1) :
    upperRosserBoundaryLogKernel s a x₀ ≤ Real.log 6 := by
  rw [upperRosserBoundaryLogKernel]
  split_ifs with hcell
  · have hden : 0 < max a (s - x₀ - 3 * a) := by
      exact (by norm_num : (0 : ℝ) < 1 / 6).trans_le
        (ha.trans (le_max_left _ _))
    apply Real.log_le_log (div_pos (hden.trans hcell) hden)
    apply (div_le_iff₀ hden).2
    nlinarith [le_max_left a (s - x₀ - 3 * a)]
  · exact Real.log_nonneg (by norm_num)

theorem measurable_upperRosserBoundaryLogKernel (s a : ℝ) :
    Measurable (upperRosserBoundaryLogKernel s a) := by
  let g : ℝ → ℝ := fun x₀ => max a (s - x₀ - 3 * a)
  have hg : Measurable g :=
    measurable_const.max
      ((measurable_const.sub measurable_id).sub measurable_const)
  rw [show upperRosserBoundaryLogKernel s a = fun x₀ =>
      if g x₀ < x₀ then Real.log (x₀ / g x₀) else 0 by
    funext x₀
    rfl]
  exact Measurable.ite (measurableSet_lt hg measurable_id)
    (measurable_id.div hg).log measurable_const

/-- Including the reciprocal outer density costs at most a further factor
`6` on the screened box. -/
theorem inv_mul_upperRosserBoundaryLogKernel_le
    {s a x₀ : ℝ} (ha : 1 / 6 ≤ a) (hax₀ : a ≤ x₀) (hx₀ : x₀ ≤ 1) :
    x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ ≤ 6 * Real.log 6 := by
  have haPos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 6).trans_le ha
  have hx₀Pos : 0 < x₀ := haPos.trans_le hax₀
  have hinv : x₀⁻¹ ≤ (6 : ℝ) := by
    calc
      x₀⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
        (inv_le_inv₀ (a := x₀) (b := (1 / 6 : ℝ)) hx₀Pos
          (by norm_num)).2 (ha.trans hax₀)
      _ = 6 := by norm_num
  exact mul_le_mul hinv
    (upperRosserBoundaryLogKernel_le_log_six ha hx₀)
    (upperRosserBoundaryLogKernel_nonneg haPos) (by norm_num)

/-- The full depth-two integrand, including its reciprocal outer weight, has a
uniform modulus of continuity on the screened ordered box. -/
theorem abs_inv_mul_upperRosserBoundaryLogKernel_sub_le
    {s a x₀ t b y₀ : ℝ}
    (ha : 1 / 6 ≤ a) (hax₀ : a ≤ x₀)
    (hb : 1 / 6 ≤ b) (hby₀ : b ≤ y₀) (hy₀ : y₀ ≤ 1) :
    |x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ -
        y₀⁻¹ * upperRosserBoundaryLogKernel t b y₀| ≤
      36 * (2 * |x₀ - y₀| + |s - t| + 4 * |a - b|) +
        36 * Real.log 6 * |x₀ - y₀| := by
  have hx₀Pos : 0 < x₀ :=
    (by norm_num : (0 : ℝ) < 1 / 6).trans_le (ha.trans hax₀)
  have hy₀Pos : 0 < y₀ :=
    (by norm_num : (0 : ℝ) < 1 / 6).trans_le (hb.trans hby₀)
  have hx₀Inv : |x₀⁻¹| ≤ 6 := by
    rw [abs_of_pos (inv_pos.mpr hx₀Pos)]
    calc
      x₀⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
        (inv_le_inv₀ hx₀Pos (by norm_num)).2 (ha.trans hax₀)
      _ = 6 := by norm_num
  have hkernelNonneg :
      0 ≤ upperRosserBoundaryLogKernel t b y₀ :=
    upperRosserBoundaryLogKernel_nonneg
      ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hb)
  have hkernelAbs :
      |upperRosserBoundaryLogKernel t b y₀| ≤ Real.log 6 := by
    rw [abs_of_nonneg hkernelNonneg]
    exact upperRosserBoundaryLogKernel_le_log_six hb hy₀
  have hkernel :=
    abs_upperRosserBoundaryLogKernel_sub_le
      (s := s) (t := t) ha hax₀ hb hby₀
  have hinv :=
    abs_inv_sub_inv_le_thirty_six_of_one_sixth_le
      (ha.trans hax₀) (hb.trans hby₀)
  calc
    |x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ -
        y₀⁻¹ * upperRosserBoundaryLogKernel t b y₀| =
        |x₀⁻¹ *
            (upperRosserBoundaryLogKernel s a x₀ -
              upperRosserBoundaryLogKernel t b y₀) +
          (x₀⁻¹ - y₀⁻¹) *
            upperRosserBoundaryLogKernel t b y₀| := by
              congr 1
              ring
    _ ≤ |x₀⁻¹| *
          |upperRosserBoundaryLogKernel s a x₀ -
            upperRosserBoundaryLogKernel t b y₀| +
        |x₀⁻¹ - y₀⁻¹| *
          |upperRosserBoundaryLogKernel t b y₀| := by
            simpa only [abs_mul] using abs_add_le
              (x₀⁻¹ *
                (upperRosserBoundaryLogKernel s a x₀ -
                  upperRosserBoundaryLogKernel t b y₀))
              ((x₀⁻¹ - y₀⁻¹) *
                upperRosserBoundaryLogKernel t b y₀)
    _ ≤ 6 * (6 *
          (2 * |x₀ - y₀| + |s - t| + 4 * |a - b|)) +
        (36 * |x₀ - y₀|) * Real.log 6 := by
          gcongr
    _ = 36 * (2 * |x₀ - y₀| + |s - t| + 4 * |a - b|) +
        36 * Real.log 6 * |x₀ - y₀| := by ring

theorem integrableOn_inv_mul_upperRosserBoundaryLogKernel
    {s a b : ℝ} (ha : 1 / 6 ≤ a) (hb : b ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀)
      (Set.Ioo a b) := by
  have hfinite : MeasureTheory.volume (Set.Ioo a b) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  apply MeasureTheory.IntegrableOn.of_bound hfinite
    (measurable_id.inv.mul
      (measurable_upperRosserBoundaryLogKernel s a)).aestronglyMeasurable
    (6 * Real.log 6)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact inv_mul_upperRosserBoundaryLogKernel_le
      ha hx₀.1.le (hx₀.2.le.trans hb)
  · exact mul_nonneg
      (inv_nonneg.mpr ((by norm_num : (0 : ℝ) < 1 / 6).le.trans
        (ha.trans hx₀.1.le)))
      (upperRosserBoundaryLogKernel_nonneg
        ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha))

/-- On a fixed screened interval, changing the sieve parameter changes the
depth-two integral by at most `36 |s - t|` times the interval length. -/
theorem abs_integral_inv_mul_upperRosserBoundaryLogKernel_sub_le
    {s t a b : ℝ} (ha : 1 / 6 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(∫ x₀ in Set.Ioo a b,
       x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) -
      ∫ x₀ in Set.Ioo a b,
       x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀| ≤
      36 * |s - t| * (b - a) := by
  let fs : ℝ → ℝ :=
    fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀
  let ft : ℝ → ℝ :=
    fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀
  have hfs : MeasureTheory.IntegrableOn fs (Set.Ioo a b) :=
    integrableOn_inv_mul_upperRosserBoundaryLogKernel ha hb
  have hft : MeasureTheory.IntegrableOn ft (Set.Ioo a b) :=
    integrableOn_inv_mul_upperRosserBoundaryLogKernel ha hb
  have hfinite : MeasureTheory.volume (Set.Ioo a b) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hnorm :
      ‖∫ x₀ in Set.Ioo a b, fs x₀ - ft x₀‖ ≤
       (36 * |s - t|) * MeasureTheory.volume.real (Set.Ioo a b) := by
    apply MeasureTheory.norm_setIntegral_le_of_norm_le_const hfinite
    intro x₀ hx₀
    rw [Real.norm_eq_abs]
    dsimp [fs, ft]
    simpa using
      (abs_inv_mul_upperRosserBoundaryLogKernel_sub_le
       (s := s) (t := t) ha hx₀.1.le ha hx₀.1.le (hx₀.2.le.trans hb))
  rw [MeasureTheory.integral_sub hfs hft, Real.norm_eq_abs,
    Real.volume_real_Ioo_of_le hab] at hnorm
  simpa [fs, ft] using hnorm

/-- On any screened interval, the depth-two integrand is bounded by its interval
length times the uniform kernel bound. -/
theorem integral_inv_mul_upperRosserBoundaryLogKernel_le_length
    {s a u v : ℝ} (ha : 1 / 6 ≤ a) (hau : a ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (∫ x₀ in Set.Ioo u v,
       x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤
      (v - u) * (6 * Real.log 6) := by
  have hf : MeasureTheory.IntegrableOn
      (fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀)
      (Set.Ioo u v) :=
    (integrableOn_inv_mul_upperRosserBoundaryLogKernel
      (s := s) ha (show (1 : ℝ) ≤ 1 from le_rfl)).mono_set (by
       intro x hx
       exact ⟨hau.trans_lt hx.1, hx.2.trans_le hv⟩)
  have hfinite : MeasureTheory.volume (Set.Ioo u v) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hconst :
      MeasureTheory.IntegrableOn (fun _ : ℝ => 6 * Real.log 6)
       (Set.Ioo u v) :=
    MeasureTheory.integrableOn_const hfinite
  calc
    (∫ x₀ in Set.Ioo u v,
       x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤
       ∫ _x₀ in Set.Ioo u v, 6 * Real.log 6 := by
      apply MeasureTheory.setIntegral_mono_on hf hconst measurableSet_Ioo
      intro x₀ hx₀
      exact inv_mul_upperRosserBoundaryLogKernel_le
       ha (hau.trans_lt hx₀.1).le (hx₀.2.le.trans hv)
    _ = (v - u) * (6 * Real.log 6) := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
       Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)]
      rfl

/-- The cells meeting the moving outer face `x₀ = s / 3` contribute only
`O(h)`, uniformly in `s`.  This is the remaining boundary-strip estimate in the
depth-two Darboux comparison. -/
theorem integral_inv_mul_upperRosserBoundaryLogKernel_moving_strip_le
    {s a h : ℝ} (ha : 1 / 6 ≤ a) (hh : 0 ≤ h) :
    (∫ x₀ in Set.Ioo (max a (s / 3 - h)) (min 1 (s / 3 + h)),
       x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤
      12 * h * Real.log 6 := by
  by_cases huv : max a (s / 3 - h) ≤ min 1 (s / 3 + h)
  · have hlength :
       min 1 (s / 3 + h) - max a (s / 3 - h) ≤ 2 * h := by
      linarith [min_le_right (1 : ℝ) (s / 3 + h),
       le_max_right a (s / 3 - h)]
    have hbound :=
      integral_inv_mul_upperRosserBoundaryLogKernel_le_length
       (s := s) ha (le_max_left _ _) huv (min_le_left _ _)
    have hcoefficient : 0 ≤ 6 * Real.log 6 :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
    calc
      (∫ x₀ in Set.Ioo (max a (s / 3 - h)) (min 1 (s / 3 + h)),
         x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤
         (min 1 (s / 3 + h) - max a (s / 3 - h)) *
           (6 * Real.log 6) := hbound
      _ ≤ (2 * h) * (6 * Real.log 6) :=
       mul_le_mul_of_nonneg_right hlength hcoefficient
      _ = 12 * h * Real.log 6 := by ring
  · have hempty :
       Set.Ioo (max a (s / 3 - h)) (min 1 (s / 3 + h)) = ∅ :=
      Set.Ioo_eq_empty (not_lt_of_ge (not_le.mp huv).le)
    rw [hempty, MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hh) (Real.log_nonneg (by norm_num))

/-- The first positive-depth continuous boundary mass is uniformly Lipschitz in
the sieve parameter on the screened outer range.  The `36` term controls the
kernel on the common support, while `2 log 6` is the moving-face strip cost. -/
theorem abs_upperRosserBoundaryMass_one_sub_le
    {s t a : ℝ} (ha : 1 / 6 ≤ a) :
    |upperRosserBoundaryMass 1 s a - upperRosserBoundaryMass 1 t a| ≤
      (36 + 2 * Real.log 6) * |s - t| := by
  suffices hordered : ∀ {s t : ℝ}, s ≤ t →
      |upperRosserBoundaryMass 1 s a -
          upperRosserBoundaryMass 1 t a| ≤
        (36 + 2 * Real.log 6) * (t - s) by
    rcases le_total s t with hst | hts
    · simpa [abs_of_nonpos (sub_nonpos.mpr hst)] using hordered hst
    · rw [abs_sub_comm]
      simpa [abs_of_nonneg (sub_nonneg.mpr hts)] using hordered hts
  intro s t hst
  let bs : ℝ := min 1 (s / 3)
  let bt : ℝ := min 1 (t / 3)
  have hbst : bs ≤ bt := by
    dsimp [bs, bt]
    exact min_le_min le_rfl (div_le_div_of_nonneg_right hst (by norm_num))
  have hbt : bt ≤ 1 := min_le_left _ _
  have hbs : bs ≤ 1 := hbst.trans hbt
  have hwidth : bt - bs ≤ (t - s) / 3 := by
    by_cases ht : t / 3 ≤ 1
    · have hs : s / 3 ≤ 1 := (div_le_div_of_nonneg_right hst (by norm_num)).trans ht
      simp only [bs, bt, min_eq_right hs, min_eq_right ht]
      ring_nf
      exact le_rfl
    · have ht' : 1 ≤ t / 3 := le_of_not_ge ht
      by_cases hs : s / 3 ≤ 1
      · simp only [bs, bt, min_eq_right hs, min_eq_left ht']
        linarith
      · have hs' : 1 ≤ s / 3 := le_of_not_ge hs
        simp only [bs, bt, min_eq_left hs', min_eq_left ht']
        linarith
  have hlog : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  by_cases hbta : bt ≤ a
  · have hbsa : bs ≤ a := hbst.trans hbta
    rw [upperRosserBoundaryMass_one_eq_integral_logKernel
        ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha),
      upperRosserBoundaryMass_one_eq_integral_logKernel
        ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha)]
    change |(∫ x₀ in Set.Ioo a bs,
        x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) -
      ∫ x₀ in Set.Ioo a bt,
        x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀| ≤ _
    rw [Set.Ioo_eq_empty (not_lt_of_ge hbsa),
      Set.Ioo_eq_empty (not_lt_of_ge hbta)]
    simp only [MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure, sub_self, abs_zero]
    exact mul_nonneg (by nlinarith) (sub_nonneg.mpr hst)
  · have habt : a < bt := lt_of_not_ge hbta
    by_cases hbsa : bs ≤ a
    · rw [upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha),
        upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha)]
      change |(∫ x₀ in Set.Ioo a bs,
          x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) -
        ∫ x₀ in Set.Ioo a bt,
          x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀| ≤ _
      rw [Set.Ioo_eq_empty (not_lt_of_ge hbsa),
        MeasureTheory.Measure.restrict_empty,
        MeasureTheory.integral_zero_measure, zero_sub, abs_neg]
      have hmassNonneg :
          0 ≤ ∫ x₀ in Set.Ioo a bt,
            x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀ := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
        exact mul_nonneg
          (inv_nonneg.mpr
            ((by norm_num : (0 : ℝ) < 1 / 6).le.trans (ha.trans hx₀.1.le)))
          (upperRosserBoundaryLogKernel_nonneg
            ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha))
      rw [abs_of_nonneg hmassNonneg]
      have htail :=
        integral_inv_mul_upperRosserBoundaryLogKernel_le_length
          (s := t) ha le_rfl habt.le hbt
      have hlength : bt - a ≤ (t - s) / 3 := by linarith
      have hscaled :
          (bt - a) * (6 * Real.log 6) ≤
            ((t - s) / 3) * (6 * Real.log 6) :=
        mul_le_mul_of_nonneg_right hlength
          (mul_nonneg (by norm_num) hlog)
      calc
        (∫ x₀ in Set.Ioo a bt,
            x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀) ≤
            (bt - a) * (6 * Real.log 6) := htail
        _ ≤ ((t - s) / 3) * (6 * Real.log 6) := hscaled
        _ ≤ (36 + 2 * Real.log 6) * (t - s) := by
          have hts : 0 ≤ t - s := sub_nonneg.mpr hst
          nlinarith
    · have habs : a < bs := lt_of_not_ge hbsa
      let fs : ℝ → ℝ :=
        fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀
      let ft : ℝ → ℝ :=
        fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel t a x₀
      have hftABs : MeasureTheory.IntegrableOn ft (Set.Ioo a bs) :=
        integrableOn_inv_mul_upperRosserBoundaryLogKernel ha hbs
      have hftBsBt : MeasureTheory.IntegrableOn ft (Set.Ioo bs bt) :=
        (integrableOn_inv_mul_upperRosserBoundaryLogKernel
          (s := t) ha hbt).mono_set (by
            intro x hx
            exact ⟨habs.trans hx.1, hx.2⟩)
      have hftABsInterval :
          IntervalIntegrable ft MeasureTheory.volume a bs :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le habs.le).mpr hftABs
      have hftBsBtInterval :
          IntervalIntegrable ft MeasureTheory.volume bs bt :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hbst).mpr hftBsBt
      have hdecomp :
          (∫ x₀ in Set.Ioo a bt, ft x₀) =
            (∫ x₀ in Set.Ioo a bs, ft x₀) +
              ∫ x₀ in Set.Ioo bs bt, ft x₀ := by
        calc
          (∫ x₀ in Set.Ioo a bt, ft x₀) =
              ∫ x₀ in a..bt, ft x₀ := by
                rw [intervalIntegral.integral_of_le habt.le,
                  MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ = (∫ x₀ in a..bs, ft x₀) +
                ∫ x₀ in bs..bt, ft x₀ :=
            (intervalIntegral.integral_add_adjacent_intervals
              hftABsInterval hftBsBtInterval).symm
          _ = (∫ x₀ in Set.Ioo a bs, ft x₀) +
                ∫ x₀ in Set.Ioo bs bt, ft x₀ := by
            rw [intervalIntegral.integral_of_le habs.le,
              MeasureTheory.integral_Ioc_eq_integral_Ioo,
              intervalIntegral.integral_of_le hbst,
              MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have hcommon :=
        abs_integral_inv_mul_upperRosserBoundaryLogKernel_sub_le
          (s := s) (t := t) ha habs.le hbs
      have hcommon' :
          |(∫ x₀ in Set.Ioo a bs, fs x₀) -
              ∫ x₀ in Set.Ioo a bs, ft x₀| ≤ 36 * (t - s) := by
        have hlength : bs - a ≤ 1 := by
          have haNonneg : 0 ≤ a :=
            (by norm_num : (0 : ℝ) ≤ 1 / 6).trans ha
          linarith
        have hts : 0 ≤ t - s := sub_nonneg.mpr hst
        calc
          |(∫ x₀ in Set.Ioo a bs, fs x₀) -
              ∫ x₀ in Set.Ioo a bs, ft x₀| ≤
              36 * |s - t| * (bs - a) := by
                simpa [fs, ft] using hcommon
          _ = 36 * (t - s) * (bs - a) := by
            rw [abs_of_nonpos (sub_nonpos.mpr hst)]
            ring
          _ ≤ 36 * (t - s) := by nlinarith
      have htail :=
        integral_inv_mul_upperRosserBoundaryLogKernel_le_length
          (s := t) ha habs.le hbst hbt
      have htailNonneg :
          0 ≤ ∫ x₀ in Set.Ioo bs bt, ft x₀ := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
        dsimp [ft]
        exact mul_nonneg
          (inv_nonneg.mpr
            ((by norm_num : (0 : ℝ) < 1 / 6).le.trans
              (ha.trans (habs.trans hx₀.1).le)))
          (upperRosserBoundaryLogKernel_nonneg
            ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha))
      have htail' :
          |∫ x₀ in Set.Ioo bs bt, ft x₀| ≤
            2 * Real.log 6 * (t - s) := by
        rw [abs_of_nonneg htailNonneg]
        have hscaled :
            (bt - bs) * (6 * Real.log 6) ≤
              ((t - s) / 3) * (6 * Real.log 6) :=
          mul_le_mul_of_nonneg_right hwidth
            (mul_nonneg (by norm_num) hlog)
        calc
          (∫ x₀ in Set.Ioo bs bt, ft x₀) ≤
              (bt - bs) * (6 * Real.log 6) := by
                simpa [ft] using htail
          _ ≤ ((t - s) / 3) * (6 * Real.log 6) := hscaled
          _ = 2 * Real.log 6 * (t - s) := by ring
      rw [upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha),
        upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha)]
      change |(∫ x₀ in Set.Ioo a bs, fs x₀) -
        ∫ x₀ in Set.Ioo a bt, ft x₀| ≤ _
      rw [hdecomp]
      calc
        |(∫ x₀ in Set.Ioo a bs, fs x₀) -
            ((∫ x₀ in Set.Ioo a bs, ft x₀) +
              ∫ x₀ in Set.Ioo bs bt, ft x₀)| =
            |((∫ x₀ in Set.Ioo a bs, fs x₀) -
              ∫ x₀ in Set.Ioo a bs, ft x₀) -
                ∫ x₀ in Set.Ioo bs bt, ft x₀| := by ring_nf
        _ ≤ |(∫ x₀ in Set.Ioo a bs, fs x₀) -
              ∫ x₀ in Set.Ioo a bs, ft x₀| +
                |∫ x₀ in Set.Ioo bs bt, ft x₀| := abs_sub _ _
        _ ≤ 36 * (t - s) + 2 * Real.log 6 * (t - s) :=
          add_le_add hcommon' htail'
        _ = (36 + 2 * Real.log 6) * (t - s) := by ring

/-- The first positive-depth boundary mass is also uniformly Lipschitz in its
screened outer cutoff.  This is the second coordinate estimate needed for the
outer `(q,p₀)` Darboux mesh. -/
theorem abs_upperRosserBoundaryMass_one_sub_le_of_outer
    {s a b : ℝ} (ha : 1 / 6 ≤ a) (hb : 1 / 6 ≤ b) :
    |upperRosserBoundaryMass 1 s a - upperRosserBoundaryMass 1 s b| ≤
      (144 + 6 * Real.log 6) * |a - b| := by
  suffices hordered : ∀ {a b : ℝ}, 1 / 6 ≤ a → a ≤ b →
      |upperRosserBoundaryMass 1 s a -
          upperRosserBoundaryMass 1 s b| ≤
        (144 + 6 * Real.log 6) * (b - a) by
    rcases le_total a b with hab | hba
    · simpa [abs_of_nonpos (sub_nonpos.mpr hab)] using hordered ha hab
    · rw [abs_sub_comm]
      simpa [abs_of_nonneg (sub_nonneg.mpr hba)] using hordered hb hba
  intro a b ha hab
  let c : ℝ := min 1 (s / 3)
  have hc : c ≤ 1 := min_le_left _ _
  have hlog : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  by_cases hca : c ≤ a
  · have hcb : c ≤ b := hca.trans hab
    rw [upperRosserBoundaryMass_one_eq_integral_logKernel
        ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha),
      upperRosserBoundaryMass_one_eq_integral_logKernel
        ((by norm_num : (0 : ℝ) < 1 / 6).trans_le
          ((show 1 / 6 ≤ b from ha.trans hab)))]
    change |(∫ x₀ in Set.Ioo a c,
        x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) -
      ∫ x₀ in Set.Ioo b c,
        x₀⁻¹ * upperRosserBoundaryLogKernel s b x₀| ≤ _
    rw [Set.Ioo_eq_empty (not_lt_of_ge hca),
      Set.Ioo_eq_empty (not_lt_of_ge hcb)]
    simp only [MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure, sub_self, abs_zero]
    exact mul_nonneg (by nlinarith) (sub_nonneg.mpr hab)
  · have hac : a < c := lt_of_not_ge hca
    by_cases hcb : c ≤ b
    · rw [upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha),
        upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le (ha.trans hab))]
      change |(∫ x₀ in Set.Ioo a c,
          x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) -
        ∫ x₀ in Set.Ioo b c,
          x₀⁻¹ * upperRosserBoundaryLogKernel s b x₀| ≤ _
      rw [Set.Ioo_eq_empty (not_lt_of_ge hcb),
        MeasureTheory.Measure.restrict_empty,
        MeasureTheory.integral_zero_measure, sub_zero]
      have hmassNonneg :
          0 ≤ ∫ x₀ in Set.Ioo a c,
            x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
        exact mul_nonneg
          (inv_nonneg.mpr
            ((by norm_num : (0 : ℝ) < 1 / 6).le.trans
              (ha.trans hx₀.1.le)))
          (upperRosserBoundaryLogKernel_nonneg
            ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha))
      rw [abs_of_nonneg hmassNonneg]
      have htail :=
        integral_inv_mul_upperRosserBoundaryLogKernel_le_length
          (s := s) ha le_rfl hac.le hc
      have hlength : c - a ≤ b - a := by linarith
      have hscaled :
          (c - a) * (6 * Real.log 6) ≤
            (b - a) * (6 * Real.log 6) :=
        mul_le_mul_of_nonneg_right hlength
          (mul_nonneg (by norm_num) hlog)
      calc
        (∫ x₀ in Set.Ioo a c,
            x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤
            (c - a) * (6 * Real.log 6) := htail
        _ ≤ (b - a) * (6 * Real.log 6) := hscaled
        _ ≤ (144 + 6 * Real.log 6) * (b - a) := by
          have hba : 0 ≤ b - a := sub_nonneg.mpr hab
          nlinarith
    · have hbc : b < c := lt_of_not_ge hcb
      let fa : ℝ → ℝ :=
        fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀
      let fb : ℝ → ℝ :=
        fun x₀ => x₀⁻¹ * upperRosserBoundaryLogKernel s b x₀
      have hfaAB : MeasureTheory.IntegrableOn fa (Set.Ioo a b) :=
        (integrableOn_inv_mul_upperRosserBoundaryLogKernel
          (s := s) ha hc).mono_set (by
            intro x hx
            exact ⟨hx.1, hx.2.trans hbc⟩)
      have hfaBC : MeasureTheory.IntegrableOn fa (Set.Ioo b c) :=
        (integrableOn_inv_mul_upperRosserBoundaryLogKernel
          (s := s) ha hc).mono_set (by
            intro x hx
            exact ⟨hab.trans_lt hx.1, hx.2⟩)
      have hfaABInterval :
          IntervalIntegrable fa MeasureTheory.volume a b :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hfaAB
      have hfaBCInterval :
          IntervalIntegrable fa MeasureTheory.volume b c :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hbc.le).mpr hfaBC
      have hdecomp :
          (∫ x₀ in Set.Ioo a c, fa x₀) =
            (∫ x₀ in Set.Ioo a b, fa x₀) +
              ∫ x₀ in Set.Ioo b c, fa x₀ := by
        calc
          (∫ x₀ in Set.Ioo a c, fa x₀) =
              ∫ x₀ in a..c, fa x₀ := by
                rw [intervalIntegral.integral_of_le hac.le,
                  MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ = (∫ x₀ in a..b, fa x₀) +
                ∫ x₀ in b..c, fa x₀ :=
            (intervalIntegral.integral_add_adjacent_intervals
              hfaABInterval hfaBCInterval).symm
          _ = (∫ x₀ in Set.Ioo a b, fa x₀) +
                ∫ x₀ in Set.Ioo b c, fa x₀ := by
            rw [intervalIntegral.integral_of_le hab,
              MeasureTheory.integral_Ioc_eq_integral_Ioo,
              intervalIntegral.integral_of_le hbc.le,
              MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have hfinite : MeasureTheory.volume (Set.Ioo b c) < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top
      have hcommon :
          |(∫ x₀ in Set.Ioo b c, fa x₀) -
              ∫ x₀ in Set.Ioo b c, fb x₀| ≤ 144 * (b - a) := by
        have hnorm :
            ‖∫ x₀ in Set.Ioo b c, fa x₀ - fb x₀‖ ≤
              (144 * (b - a)) *
                MeasureTheory.volume.real (Set.Ioo b c) := by
          apply MeasureTheory.norm_setIntegral_le_of_norm_le_const hfinite
          intro x₀ hx₀
          rw [Real.norm_eq_abs]
          dsimp [fa, fb]
          have hpoint :=
            abs_inv_mul_upperRosserBoundaryLogKernel_sub_le
              (s := s) (t := s) ha (hab.trans hx₀.1.le)
                (ha.trans hab) hx₀.1.le (hx₀.2.le.trans hc)
          calc
            |x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀ -
                x₀⁻¹ * upperRosserBoundaryLogKernel s b x₀| ≤
                36 * (2 * |x₀ - x₀| + |s - s| + 4 * |a - b|) +
                  36 * Real.log 6 * |x₀ - x₀| := hpoint
            _ = 144 * (b - a) := by
              simp only [sub_self, abs_zero, add_zero,
                abs_of_nonpos (sub_nonpos.mpr hab)]
              ring
        have hfaBC' : MeasureTheory.IntegrableOn fa (Set.Ioo b c) := hfaBC
        have hfbBC : MeasureTheory.IntegrableOn fb (Set.Ioo b c) :=
          integrableOn_inv_mul_upperRosserBoundaryLogKernel (ha.trans hab) hc
        rw [MeasureTheory.integral_sub hfaBC' hfbBC, Real.norm_eq_abs,
          Real.volume_real_Ioo_of_le hbc.le] at hnorm
        have hlength : c - b ≤ 1 := by
          have hbNonneg : 0 ≤ b :=
            (by norm_num : (0 : ℝ) ≤ 1 / 6).trans (ha.trans hab)
          linarith
        have hba : 0 ≤ b - a := sub_nonneg.mpr hab
        calc
          |(∫ x₀ in Set.Ioo b c, fa x₀) -
              ∫ x₀ in Set.Ioo b c, fb x₀| ≤
              (144 * (b - a)) * (c - b) := hnorm
          _ ≤ 144 * (b - a) := by nlinarith
      have hlower :=
        integral_inv_mul_upperRosserBoundaryLogKernel_le_length
          (s := s) ha le_rfl hab (hbc.le.trans hc)
      have hlowerNonneg :
          0 ≤ ∫ x₀ in Set.Ioo a b, fa x₀ := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
        dsimp [fa]
        exact mul_nonneg
          (inv_nonneg.mpr
            ((by norm_num : (0 : ℝ) < 1 / 6).le.trans
              (ha.trans hx₀.1.le)))
          (upperRosserBoundaryLogKernel_nonneg
            ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha))
      have hlower' :
          |∫ x₀ in Set.Ioo a b, fa x₀| ≤
            6 * Real.log 6 * (b - a) := by
        rw [abs_of_nonneg hlowerNonneg]
        calc
          (∫ x₀ in Set.Ioo a b, fa x₀) ≤
              (b - a) * (6 * Real.log 6) := by
                simpa [fa] using hlower
          _ = 6 * Real.log 6 * (b - a) := by ring
      rw [upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le ha),
        upperRosserBoundaryMass_one_eq_integral_logKernel
          ((by norm_num : (0 : ℝ) < 1 / 6).trans_le (ha.trans hab))]
      change |(∫ x₀ in Set.Ioo a c, fa x₀) -
        ∫ x₀ in Set.Ioo b c, fb x₀| ≤ _
      rw [hdecomp]
      calc
        |((∫ x₀ in Set.Ioo a b, fa x₀) +
            ∫ x₀ in Set.Ioo b c, fa x₀) -
              ∫ x₀ in Set.Ioo b c, fb x₀| =
            |(∫ x₀ in Set.Ioo a b, fa x₀) +
              ((∫ x₀ in Set.Ioo b c, fa x₀) -
                ∫ x₀ in Set.Ioo b c, fb x₀)| := by ring_nf
        _ ≤ |∫ x₀ in Set.Ioo a b, fa x₀| +
            |(∫ x₀ in Set.Ioo b c, fa x₀) -
              ∫ x₀ in Set.Ioo b c, fb x₀| := abs_add_le _ _
        _ ≤ 6 * Real.log 6 * (b - a) + 144 * (b - a) :=
          add_le_add hlower' hcommon
        _ = (144 + 6 * Real.log 6) * (b - a) := by ring

/-- Joint modulus of continuity for the depth-two boundary mass in its sieve
parameter and outer coordinate. -/
theorem abs_upperRosserBoundaryMass_one_sub_le_joint
    {s t a b : ℝ} (ha : 1 / 6 ≤ a) (hb : 1 / 6 ≤ b) :
    |upperRosserBoundaryMass 1 s a - upperRosserBoundaryMass 1 t b| ≤
      (36 + 2 * Real.log 6) * |s - t| +
        (144 + 6 * Real.log 6) * |a - b| := by
  calc
    |upperRosserBoundaryMass 1 s a -
        upperRosserBoundaryMass 1 t b| =
        |(upperRosserBoundaryMass 1 s a -
            upperRosserBoundaryMass 1 t a) +
          (upperRosserBoundaryMass 1 t a -
            upperRosserBoundaryMass 1 t b)| := by ring_nf
    _ ≤ |upperRosserBoundaryMass 1 s a -
          upperRosserBoundaryMass 1 t a| +
        |upperRosserBoundaryMass 1 t a -
          upperRosserBoundaryMass 1 t b| := abs_add_le _ _
    _ ≤ (36 + 2 * Real.log 6) * |s - t| +
        (144 + 6 * Real.log 6) * |a - b| :=
      add_le_add (abs_upperRosserBoundaryMass_one_sub_le ha)
        (abs_upperRosserBoundaryMass_one_sub_le_of_outer ha hb)

/-- The square reciprocal outer density is uniformly Lipschitz on
`[1/6, ∞)`. -/
theorem abs_inv_mul_inv_sub_le_four_hundred_thirty_two
    {a b : ℝ} (ha : 1 / 6 ≤ a) (hb : 1 / 6 ≤ b) :
    |a⁻¹ * a⁻¹ - b⁻¹ * b⁻¹| ≤ 432 * |a - b| := by
  have haPos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 6).trans_le ha
  have hbPos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hb
  have haInv : |a⁻¹| ≤ 6 := by
    rw [abs_of_pos (inv_pos.mpr haPos)]
    calc
      a⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
        (inv_le_inv₀ haPos (by norm_num)).2 ha
      _ = 6 := by norm_num
  have hbInv : |b⁻¹| ≤ 6 := by
    rw [abs_of_pos (inv_pos.mpr hbPos)]
    calc
      b⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
        (inv_le_inv₀ hbPos (by norm_num)).2 hb
      _ = 6 := by norm_num
  have hdiff : |a⁻¹ - b⁻¹| ≤ 36 * |a - b| :=
    abs_inv_sub_inv_le_thirty_six_of_one_sixth_le ha hb
  have hsum : |a⁻¹ + b⁻¹| ≤ 12 :=
    (abs_add_le a⁻¹ b⁻¹).trans (by linarith)
  calc
    |a⁻¹ * a⁻¹ - b⁻¹ * b⁻¹| =
        |(a⁻¹ - b⁻¹) * (a⁻¹ + b⁻¹)| := by
          congr 1
          ring
    _ = |a⁻¹ - b⁻¹| * |a⁻¹ + b⁻¹| := abs_mul _ _
    _ ≤ (36 * |a - b|) * |a⁻¹ + b⁻¹| :=
      mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
    _ ≤ (36 * |a - b|) * 12 := by
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by norm_num) (abs_nonneg _))
    _ = 432 * |a - b| := by ring

/-- Uniform depth-two boundary-mass bound on the screened outer range.  The
factor `5` uses that the outer interval has length at most `1 - 1 / 6`. -/
theorem upperRosserBoundaryMass_one_le_five_mul_log_six
    {s a : ℝ} (ha : 1 / 6 ≤ a) :
    upperRosserBoundaryMass 1 s a ≤ 5 * Real.log 6 := by
  have haPos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 6).trans_le ha
  rw [upperRosserBoundaryMass_one_eq_integral_logKernel haPos]
  let b := min 1 (s / 3)
  change (∫ x₀ in Set.Ioo a b,
    x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤ 5 * Real.log 6
  by_cases hab : a < b
  · have hf := integrableOn_inv_mul_upperRosserBoundaryLogKernel
      (s := s) ha (show b ≤ 1 from min_le_left _ _)
    have hfinite : MeasureTheory.volume (Set.Ioo a b) ≠ ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ => 6 * Real.log 6)
          (Set.Ioo a b) :=
      MeasureTheory.integrableOn_const hfinite
    calc
      (∫ x₀ in Set.Ioo a b,
          x₀⁻¹ * upperRosserBoundaryLogKernel s a x₀) ≤
          ∫ _x₀ in Set.Ioo a b, 6 * Real.log 6 := by
        apply MeasureTheory.setIntegral_mono_on hf hconst measurableSet_Ioo
        intro x₀ hx₀
        exact inv_mul_upperRosserBoundaryLogKernel_le
          ha hx₀.1.le (hx₀.2.le.trans (min_le_left _ _))
      _ = (b - a) * (6 * Real.log 6) := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
        rfl
      _ ≤ 5 * Real.log 6 := by
        have hb : b ≤ 1 := min_le_left _ _
        have hlog : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
        nlinarith
  · rw [Set.Ioo_eq_empty hab, MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))

/-- Every finite-depth continuous boundary mass is nonnegative once its terminal
coordinate is nonnegative. -/
theorem upperRosserBoundaryMassAux_nonneg (k : ℕ) {s a b : ℝ} (ha : 0 ≤ a) :
    0 ≤ upperRosserBoundaryMassAux k s a b := by
  induction k generalizing s b with
  | zero =>
      simp only [upperRosserBoundaryMassAux_zero]
      split_ifs <;> norm_num
  | succ k ih =>
      rw [upperRosserBoundaryMassAux_succ]
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
      apply mul_nonneg
      · exact inv_nonneg.mpr (ha.trans hx₀.1.le)
      · apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
        exact mul_nonneg (inv_nonneg.mpr (ha.trans hx₁.1.le)) ih

theorem upperRosserBoundaryMass_nonneg (k : ℕ) {s a : ℝ} (ha : 0 ≤ a) :
    0 ≤ upperRosserBoundaryMass k s a :=
  upperRosserBoundaryMassAux_nonneg k ha


end MathlibNt.SieveTheory.LinearSieve
