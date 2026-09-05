import MathlibNt.SieveTheory.LinearSieve.BoundaryRegularity

/-!
# Upper Rosser boundary integrals and alternating pairs

Screened integrands, support restrictions, finite boundary factors,
alternating-pair transforms, and summable prefix-volume majorants.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-- Uniform bound for the full screened depth-two outer integrand, including
both reciprocal factors in the future outer `a`-integral. -/
theorem inv_sq_mul_upperRosserBoundaryMass_one_le
    {s a : ℝ} (ha : 1 / 6 ≤ a) :
    a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a ≤ 180 * Real.log 6 := by
  have haPos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 6).trans_le ha
  have hinv : a⁻¹ ≤ (6 : ℝ) := by
    calc
      a⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
        (inv_le_inv₀ (a := a) (b := (1 / 6 : ℝ)) haPos
          (by norm_num)).2 ha
      _ = 6 := by norm_num
  have hinvNonneg : 0 ≤ a⁻¹ := inv_nonneg.mpr haPos.le
  have hinvSq : a⁻¹ * a⁻¹ ≤ (36 : ℝ) := by nlinarith
  calc
    a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a ≤
        36 * (5 * Real.log 6) :=
      mul_le_mul hinvSq
        (upperRosserBoundaryMass_one_le_five_mul_log_six ha)
        (upperRosserBoundaryMass_nonneg 1 haPos.le) (by norm_num)
    _ = 180 * Real.log 6 := by ring

/-- The complete depth-two outer density is jointly Lipschitz on the screened
box.  This is the uniform-continuity input for the final outer Darboux sum. -/
theorem abs_inv_sq_mul_upperRosserBoundaryMass_one_sub_le
    {s t a b : ℝ} (ha : 1 / 6 ≤ a) (hb : 1 / 6 ≤ b) :
    |a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a -
        b⁻¹ * b⁻¹ * upperRosserBoundaryMass 1 t b| ≤
      36 * ((36 + 2 * Real.log 6) * |s - t| +
        (144 + 6 * Real.log 6) * |a - b|) +
      2160 * Real.log 6 * |a - b| := by
  have haPos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 6).trans_le ha
  have hbPos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hb
  have haInv : a⁻¹ ≤ (6 : ℝ) := by
    calc
      a⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
        (inv_le_inv₀ haPos (by norm_num)).2 ha
      _ = 6 := by norm_num
  have haInvNonneg : 0 ≤ a⁻¹ := inv_nonneg.mpr haPos.le
  have haInvSq : |a⁻¹ * a⁻¹| ≤ (36 : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg haInvNonneg haInvNonneg)]
    nlinarith
  have hmass :=
    abs_upperRosserBoundaryMass_one_sub_le_joint
      (s := s) (t := t) ha hb
  have hmassNonneg :
      0 ≤ upperRosserBoundaryMass 1 t b :=
    upperRosserBoundaryMass_nonneg 1 hbPos.le
  have hmassAbs :
      |upperRosserBoundaryMass 1 t b| ≤ 5 * Real.log 6 := by
    rw [abs_of_nonneg hmassNonneg]
    exact upperRosserBoundaryMass_one_le_five_mul_log_six hb
  have hinv :=
    abs_inv_mul_inv_sub_le_four_hundred_thirty_two ha hb
  calc
    |a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a -
        b⁻¹ * b⁻¹ * upperRosserBoundaryMass 1 t b| =
        |(a⁻¹ * a⁻¹) *
           (upperRosserBoundaryMass 1 s a -
             upperRosserBoundaryMass 1 t b) +
         (a⁻¹ * a⁻¹ - b⁻¹ * b⁻¹) *
           upperRosserBoundaryMass 1 t b| := by
             congr 1
             ring
    _ ≤ |a⁻¹ * a⁻¹| *
         |upperRosserBoundaryMass 1 s a -
           upperRosserBoundaryMass 1 t b| +
        |a⁻¹ * a⁻¹ - b⁻¹ * b⁻¹| *
         |upperRosserBoundaryMass 1 t b| := by
           simpa only [abs_mul] using abs_add_le
             ((a⁻¹ * a⁻¹) *
               (upperRosserBoundaryMass 1 s a -
                 upperRosserBoundaryMass 1 t b))
             ((a⁻¹ * a⁻¹ - b⁻¹ * b⁻¹) *
               upperRosserBoundaryMass 1 t b)
    _ ≤ 36 * ((36 + 2 * Real.log 6) * |s - t| +
         (144 + 6 * Real.log 6) * |a - b|) +
        (432 * |a - b|) * (5 * Real.log 6) := by
         exact add_le_add
           (mul_le_mul haInvSq hmass (abs_nonneg _)
             (by norm_num))
           (mul_le_mul hinv hmassAbs (abs_nonneg _)
             (mul_nonneg (by norm_num) (abs_nonneg _)))
    _ = 36 * ((36 + 2 * Real.log 6) * |s - t| +
         (144 + 6 * Real.log 6) * |a - b|) +
        2160 * Real.log 6 * |a - b| := by ring

/-- For fixed `s`, the complete screened depth-two outer density is Lipschitz in
the outer logarithmic coordinate. -/
theorem lipschitzOn_inv_sq_mul_upperRosserBoundaryMass_one (s : ℝ) :
    LipschitzOnWith
      ⟨36 * (144 + 6 * Real.log 6) + 2160 * Real.log 6, by
        positivity⟩
      (fun a => a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a)
      (Set.Ici (1 / 6)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [Real.dist_eq, Real.dist_eq]
  have h :=
    abs_inv_sq_mul_upperRosserBoundaryMass_one_sub_le
      (s := s) (t := s) ha hb
  simp only [sub_self, abs_zero, mul_zero, zero_add] at h
  change
    |a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a -
        b⁻¹ * b⁻¹ * upperRosserBoundaryMass 1 s b| ≤
      (36 * (144 + 6 * Real.log 6) + 2160 * Real.log 6) * |a - b|
  calc
    |a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a -
        b⁻¹ * b⁻¹ * upperRosserBoundaryMass 1 s b| ≤
        36 * ((144 + 6 * Real.log 6) * |a - b|) +
          2160 * Real.log 6 * |a - b| := h
    _ = (36 * (144 + 6 * Real.log 6) + 2160 * Real.log 6) *
        |a - b| := by ring

/-- The screened depth-two outer density is integrable.  Together with
`integral_upperRosserBoundaryMass_one_eq_integral_one_sixth`, this places the
entire depth-two continuous contribution on a compact Lipschitz interval. -/
theorem integrableOn_inv_sq_mul_upperRosserBoundaryMass_one (s : ℝ) :
    MeasureTheory.IntegrableOn
      (fun a => a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a)
      (Set.Ioo (1 / 6) 1) := by
  let f : ℝ → ℝ :=
    fun a => a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a
  have hfinite : MeasureTheory.volume (Set.Ioo (1 / 6 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hcontinuous : ContinuousOn f (Set.Ioo (1 / 6) 1) := by
    apply
      (lipschitzOn_inv_sq_mul_upperRosserBoundaryMass_one s).continuousOn.mono
    intro a ha
    exact ha.1.le
  apply MeasureTheory.IntegrableOn.of_bound hfinite
    (hcontinuous.aestronglyMeasurable measurableSet_Ioo)
    (180 * Real.log 6)
  filter_upwards
    [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact inv_sq_mul_upperRosserBoundaryMass_one_le ha.1.le
  · exact mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr ((by norm_num : (0 : ℝ) < 1 / 6).le.trans ha.1.le))
        (inv_nonneg.mpr ((by norm_num : (0 : ℝ) < 1 / 6).le.trans ha.1.le)))
      (upperRosserBoundaryMass_nonneg 1
        ((by norm_num : (0 : ℝ) < 1 / 6).le.trans ha.1.le))

/-- The recursive continuous mass has the same depth-dependent lower support as
the exact Rosser region: at depth `2k` it vanishes unless
`s / 3^(k+1) < a`. -/
theorem upperRosserBoundaryMassAux_eq_zero_of_terminal_le
    (k : ℕ) {s a b : ℝ} (hs : 0 ≤ s) (ha : a ≤ s / 3 ^ (k + 1)) :
    upperRosserBoundaryMassAux k s a b = 0 := by
  induction k generalizing s b with
  | zero =>
      rw [upperRosserBoundaryMassAux_zero]
      rw [if_neg]
      rintro ⟨_, hsa⟩
      norm_num at ha
      linarith
  | succ k ih =>
      rw [upperRosserBoundaryMassAux_succ]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₀ hx₀
      have hx₀s : x₀ < s / 3 :=
        hx₀.2.trans_le (min_le_right b (s / 3))
      have hinner :
          (∫ x₁ in Set.Ioo a x₀,
              x₁⁻¹ *
                upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁) = 0 := by
        apply MeasureTheory.integral_eq_zero_of_ae
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x₁ hx₁
        have hrem : s / 3 < s - x₀ - x₁ := by
          linarith [hx₁.2]
        have hremnonneg : 0 ≤ s - x₀ - x₁ := by
          have hsdiv : 0 ≤ s / 3 := div_nonneg hs (by norm_num)
          linarith
        have hpow : (0 : ℝ) < 3 ^ (k + 1) := by positivity
        have hscale :
            s / 3 ^ (k + 2) ≤ (s - x₀ - x₁) / 3 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          calc
            s / (3 ^ (k + 1) * 3) = (s / 3) / 3 ^ (k + 1) := by ring
            _ ≤ (s - x₀ - x₁) / 3 ^ (k + 1) :=
              (div_le_div_iff_of_pos_right hpow).2 hrem.le
        rw [ih hremnonneg (ha.trans hscale)]
        simp
      rw [hinner]
      simp

/-- Nonvanishing of the depth-`2k` continuous residual forces its terminal
coordinate past the exact recursive support threshold. -/
theorem upperRosserBoundaryMassAux_ne_zero_terminal_lt
    (k : ℕ) {s a b : ℝ} (hs : 0 ≤ s)
    (h : upperRosserBoundaryMassAux k s a b ≠ 0) :
    s / 3 ^ (k + 1) < a :=
  lt_of_not_ge fun ha => h <|
    upperRosserBoundaryMassAux_eq_zero_of_terminal_le k hs ha

/-- After one Rosser pair has been peeled, every nonzero depth-`2k` residual
has a terminal coordinate bounded below solely in terms of the original
fundamental-lemma range and the remaining depth. -/
theorem upperRosserBoundaryMassAux_ne_zero_outer_lower
    (k : ℕ) {s a x₀ x₁ : ℝ} (hs : 3 / 2 ≤ s)
    (hx₀ : x₀ ≤ s / 3) (hx₁ : x₁ < x₀)
    (h : upperRosserBoundaryMassAux k (s - x₀ - x₁) a x₁ ≠ 0) :
    1 / (2 * 3 ^ (k + 1)) < a := by
  have hrem : s / 3 < s - x₀ - x₁ := by linarith
  have hremnonneg : 0 ≤ s - x₀ - x₁ := by
    have hsdiv : 0 ≤ s / 3 := by positivity
    linarith
  have hterminal :=
    upperRosserBoundaryMassAux_ne_zero_terminal_lt k hremnonneg h
  have hpow : (0 : ℝ) < 3 ^ (k + 1) := by positivity
  have hscaled :
      s / 3 ^ (k + 2) <
       (s - x₀ - x₁) / 3 ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    calc
      s / (3 ^ (k + 1) * 3) = (s / 3) / 3 ^ (k + 1) := by ring
      _ < (s - x₀ - x₁) / 3 ^ (k + 1) :=
       (div_lt_div_iff_of_pos_right hpow).2 hrem
  have hpow' : (0 : ℝ) < 3 ^ (k + 2) := by positivity
  calc
    1 / (2 * 3 ^ (k + 1)) = (3 / 2 : ℝ) / 3 ^ (k + 2) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      field_simp
      ring
    _ ≤ s / 3 ^ (k + 2) :=
      (div_le_div_iff_of_pos_right hpow').2 hs
    _ < (s - x₀ - x₁) / 3 ^ (k + 1) := hscaled
    _ < a := hterminal

/-- A positive-depth boundary mass vanishes unless the terminal coordinate lies
strictly below the cubic outer cutoff. -/
theorem upperRosserBoundaryMassAux_succ_eq_zero_of_div_three_le
    (k : ℕ) {s a b : ℝ} (h : s / 3 ≤ a) :
    upperRosserBoundaryMassAux (k + 1) s a b = 0 := by
  rw [upperRosserBoundaryMassAux_succ]
  have hempty : Set.Ioo a (min b (s / 3)) = ∅ :=
    Set.Ioo_eq_empty (by linarith [min_le_right b (s / 3)])
  rw [hempty, MeasureTheory.Measure.restrict_empty,
    MeasureTheory.integral_zero_measure]

/-- A positive-depth mass also vanishes when its inherited upper interval is
empty. -/
theorem upperRosserBoundaryMassAux_succ_eq_zero_of_upper_le
    (k : ℕ) {s a b : ℝ} (h : b ≤ a) :
    upperRosserBoundaryMassAux (k + 1) s a b = 0 := by
  rw [upperRosserBoundaryMassAux_succ]
  have hempty : Set.Ioo a (min b (s / 3)) = ∅ :=
    Set.Ioo_eq_empty (by linarith [min_le_left b (s / 3)])
  rw [hempty, MeasureTheory.Measure.restrict_empty,
    MeasureTheory.integral_zero_measure]

/-- Nonzero positive-depth mass forces both geometric support inequalities for
the first peeled coordinate. -/
theorem upperRosserBoundaryMassAux_succ_ne_zero_support
    (k : ℕ) {s a b : ℝ}
    (h : upperRosserBoundaryMassAux (k + 1) s a b ≠ 0) :
    a < b ∧ a < s / 3 := by
  constructor
  · exact lt_of_not_ge fun hba =>
      h (upperRosserBoundaryMassAux_succ_eq_zero_of_upper_le k hba)
  · exact lt_of_not_ge fun hsa =>
      h (upperRosserBoundaryMassAux_succ_eq_zero_of_div_three_le k hsa)

theorem upperRosserBoundaryMass_succ_eq_zero_of_div_three_le
    (k : ℕ) {s a : ℝ} (h : s / 3 ≤ a) :
    upperRosserBoundaryMass (k + 1) s a = 0 :=
  upperRosserBoundaryMassAux_succ_eq_zero_of_div_three_le k h

/-- The outer boundary integral may be restricted to the exact lower support
cutoff supplied by the recursive Rosser inequalities. -/
theorem integral_upperRosserBoundaryMass_eq_integral_support
    (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a) =
      ∫ a in Set.Ioo (s / 3 ^ (k + 1)) 1,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a := by
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioo
  · intro a ha
    exact ⟨(div_nonneg hs (by positivity)).trans_lt ha.1, ha.2⟩
  · intro a ha
    have hale : a ≤ s / 3 ^ (k + 1) := le_of_not_gt fun hlt =>
      ha.2 ⟨hlt, ha.1.2⟩
    rw [upperRosserBoundaryMass,
      upperRosserBoundaryMassAux_eq_zero_of_terminal_le k hs hale]
    simp

/-- On the fundamental-lemma range, every fixed-depth outer boundary integral is
supported in a compact interval bounded away from zero.  The lower endpoint
depends only on the depth, so this is the uniform domain for the fixed-depth
Darboux induction. -/
theorem integral_upperRosserBoundaryMass_eq_integral_fixedDepthSupport
    (k : ℕ) {s : ℝ} (hs : 3 / 2 ≤ s) :
    (∫ a in Set.Ioo 0 1,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a) =
      ∫ a in Set.Ioo (1 / (2 * 3 ^ k)) 1,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a := by
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioo
  · intro a ha
    exact ⟨(by positivity : (0 : ℝ) < 1 / (2 * 3 ^ k)).trans ha.1, ha.2⟩
  · intro a ha
    have hale : a ≤ 1 / (2 * 3 ^ k) := le_of_not_gt fun hlt =>
      ha.2 ⟨hlt, ha.1.2⟩
    have hsnonneg : 0 ≤ s := by linarith
    have hpow : (0 : ℝ) < 3 ^ (k + 1) := by positivity
    have hasupport : a ≤ s / 3 ^ (k + 1) := by
      calc
        a ≤ 1 / (2 * 3 ^ k) := hale
        _ = (3 / 2 : ℝ) / 3 ^ (k + 1) := by
          rw [pow_succ]
          field_simp
        _ ≤ s / 3 ^ (k + 1) :=
          (div_le_div_iff_of_pos_right hpow).2 hs
    rw [upperRosserBoundaryMass,
      upperRosserBoundaryMassAux_eq_zero_of_terminal_le k hsnonneg hasupport]
    simp

/-- On the upper-sieve range `s ≥ 3/2`, the complete depth-two outer integral is
already supported in the common screened interval `(1/6, 1)`. -/
theorem integral_upperRosserBoundaryMass_one_eq_integral_one_sixth
    {s : ℝ} (hs : 3 / 2 ≤ s) :
    (∫ a in Set.Ioo 0 1,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a) =
      ∫ a in Set.Ioo (1 / 6) 1,
        a⁻¹ * a⁻¹ * upperRosserBoundaryMass 1 s a := by
  convert
    integral_upperRosserBoundaryMass_eq_integral_fixedDepthSupport 1 hs using 1
  all_goals norm_num

/-- At depth `2k`, the outer boundary contribution vanishes once the normalized
level is at least `3^(k+1)`. -/
theorem integral_upperRosserBoundaryMass_eq_zero_of_pow_le
    (k : ℕ) {s : ℝ} (hs : (3 : ℝ) ^ (k + 1) ≤ s) :
    (∫ a in Set.Ioo 0 1,
      a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a) = 0 := by
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards
    [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
  have hsnonneg : 0 ≤ s := (by positivity : (0 : ℝ) < 3 ^ (k + 1)).le.trans hs
  have hpow : (0 : ℝ) < 3 ^ (k + 1) := by positivity
  have ha' : a ≤ s / 3 ^ (k + 1) := by
    apply (le_div_iff₀ hpow).2
    calc
      a * 3 ^ (k + 1) ≤ 1 * 3 ^ (k + 1) :=
        mul_le_mul_of_nonneg_right ha.2.le hpow.le
      _ ≤ s := by simpa using hs
  rw [upperRosserBoundaryMass,
    upperRosserBoundaryMassAux_eq_zero_of_terminal_le k hsnonneg ha']
  simp

/-- The first continuous boundary contribution is the reciprocal cubic-shell
integral.  This is the initial term of the finite Buchstab expansion. -/
theorem integral_upperRosserBoundaryMass_zero
    {s : ℝ} (hs : 0 < s) (hs3 : s < 3) :
    (∫ a in Set.Ioo 0 1,
      a⁻¹ * a⁻¹ * upperRosserBoundaryMass 0 s a) = 3 / s - 1 := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (g := fun a =>
    (Set.Ioi (s / 3)).indicator (fun a => a⁻¹ * a⁻¹) a)]
  · rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
    have hinter : Set.Ioo (0 : ℝ) 1 ∩ Set.Ioi (s / 3) =
        Set.Ioo (s / 3) 1 := by
      ext a
      change ((0 < a ∧ a < 1) ∧ s / 3 < a) ↔ s / 3 < a ∧ a < 1
      constructor
      · rintro ⟨⟨_, ha1⟩, hsa⟩
        exact ⟨hsa, ha1⟩
      · intro ha
        exact ⟨⟨(div_pos hs (by norm_num)).trans ha.1, ha.2⟩, ha.1⟩
    rw [hinter, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : s / 3 ≤ 1)]
    have hzero : (0 : ℝ) ∉ Set.uIcc (s / 3) 1 := by
      rw [Set.uIcc_of_le (by linarith : s / 3 ≤ 1)]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (by linarith)
    rw [show (fun a : ℝ => a⁻¹ * a⁻¹) =
        (fun a : ℝ => a ^ (-2 : ℤ)) by
      funext a
      simp [zpow_neg, pow_two],
      integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    norm_num [zpow_neg, hs.ne']
    field_simp [hs.ne']
    ring
  · intro a ha
    change a⁻¹ * a⁻¹ * upperRosserBoundaryMass 0 s a =
      (Set.Ioi (s / 3)).indicator (fun a => a⁻¹ * a⁻¹) a
    rw [upperRosserBoundaryMass_zero]
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h₁ h₂
    · simp
    · exfalso
      apply h₂
      linarith [h₁.2]
    · exfalso
      apply h₁
      exact ⟨hs.le, by linarith⟩
    · simp

/-- The finite continuous upper Rosser factor obtained by summing boundary
depths below `L` and then integrating the distinguished outer coordinate. -/
noncomputable def upperRosserFiniteBoundaryFactor (L : ℕ) (s : ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.range L,
    ∫ a in Set.Ioo 0 1,
      a⁻¹ * a⁻¹ * upperRosserBoundaryMass k s a

@[simp]
theorem upperRosserFiniteBoundaryFactor_zero (s : ℝ) :
    upperRosserFiniteBoundaryFactor 0 s = 1 := by
  simp [upperRosserFiniteBoundaryFactor]

/-- Adding one admissible depth adds exactly its outer-coordinate boundary
integral. -/
theorem upperRosserFiniteBoundaryFactor_succ (L : ℕ) (s : ℝ) :
    upperRosserFiniteBoundaryFactor (L + 1) s =
      upperRosserFiniteBoundaryFactor L s +
        ∫ a in Set.Ioo 0 1,
          a⁻¹ * a⁻¹ * upperRosserBoundaryMass L s a := by
  simp only [upperRosserFiniteBoundaryFactor, Finset.sum_range_succ]
  ring

/-- Every finite truncation of the continuous upper Rosser factor is
nonnegative. -/
theorem upperRosserFiniteBoundaryFactor_nonneg (L : ℕ) (s : ℝ) :
    0 ≤ upperRosserFiniteBoundaryFactor L s := by
  unfold upperRosserFiniteBoundaryFactor
  apply add_nonneg zero_le_one
  apply Finset.sum_nonneg
  intro k hk
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards
    [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr ha.1.le) (inv_nonneg.mpr ha.1.le))
    (upperRosserBoundaryMass_nonneg k ha.1.le)

/-- The finite continuous factors increase with the depth cutoff. -/
theorem upperRosserFiniteBoundaryFactor_mono_succ (L : ℕ) (s : ℝ) :
    upperRosserFiniteBoundaryFactor L s ≤
      upperRosserFiniteBoundaryFactor (L + 1) s := by
  rw [upperRosserFiniteBoundaryFactor_succ]
  exact le_add_of_nonneg_right <| by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr ha.1.le) (inv_nonneg.mpr ha.1.le))
      (upperRosserBoundaryMass_nonneg L ha.1.le)

/-- A depth contributes nothing to the finite factor once its geometric support
cutoff lies beyond the normalized sieve level. -/
theorem upperRosserFiniteBoundaryFactor_succ_eq_self_of_pow_le
    (L : ℕ) {s : ℝ} (hs : (3 : ℝ) ^ (L + 1) ≤ s) :
    upperRosserFiniteBoundaryFactor (L + 1) s =
      upperRosserFiniteBoundaryFactor L s := by
  rw [upperRosserFiniteBoundaryFactor_succ,
    integral_upperRosserBoundaryMass_eq_zero_of_pow_le L hs, add_zero]

/-- The first finite Buchstab truncation is `3 / s` on the nonempty range of
the cubic shell. -/
theorem upperRosserFiniteBoundaryFactor_one
    {s : ℝ} (hs : 0 < s) (hs3 : s < 3) :
    upperRosserFiniteBoundaryFactor 1 s = 3 / s := by
  calc
    upperRosserFiniteBoundaryFactor 1 s =
        upperRosserFiniteBoundaryFactor 0 s +
          ∫ a in Set.Ioo 0 1,
            a⁻¹ * a⁻¹ * upperRosserBoundaryMass 0 s a := by
      simpa using upperRosserFiniteBoundaryFactor_succ 0 s
    _ = 3 / s := by
      rw [upperRosserFiniteBoundaryFactor_zero,
        integral_upperRosserBoundaryMass_zero hs hs3]
      ring

/-- Combining an even Rosser prefix inequality with the terminal boundary
inequality gives a constraint from that coordinate towards the *remaining*
suffix.  Unlike the unrestricted factorial estimate, this retains every
alternating-prefix condition. -/
theorem UpperRosserLogRegion.even_coordinate_lt_suffix_add_terminal
    {s a : ℝ} {x : List ℝ} (hregion : UpperRosserLogRegion s a x)
    {i : ℕ} (hi : i < x.length) (heven : Even i) :
    2 * x[i] < (x.drop (i + 1)).sum + 3 * a := by
  have hpref := hregion.2.2.2.1 i hi heven
  have hterminal := hregion.2.2.2.2
  have hsum := List.sum_take_add_sum_drop x (i + 1)
  rw [List.sum_take_succ x i hi] at hsum
  linarith

/-- At the innermost pair of a nonempty even Rosser chain, the larger coordinate
is less than half the smaller coordinate plus the terminal budget. -/
theorem UpperRosserLogRegion.last_pair_lt_terminal
    {s a : ℝ} {x : List ℝ} {k : ℕ}
    (hregion : UpperRosserLogRegion s a x)
    (hlen : x.length = 2 * (k + 1)) :
    2 * x[2 * k] < x[2 * k + 1] + 3 * a := by
  have hi : 2 * k < x.length := by omega
  have h := hregion.even_coordinate_lt_suffix_add_terminal hi (by simp)
  have hdrop : x.drop (2 * k + 1) = [x[2 * k + 1]] := by
    apply List.ext_getElem
    · simp [hlen]
      omega
    · intro n hn₁ hn₂
      have hn : n = 0 := by
        simp only [List.length_drop] at hn₁
        omega
      subst n
      simp
  rw [hdrop] at h
  simpa using h

/-- After division by the terminal coordinate, the innermost Rosser pair lies in
the scale-free triangular region
`1 < y < 3`, `y < x < (y + 3) / 2`.  This is the first cell of the
reverse-chain geometric contraction below. -/
theorem UpperRosserLogRegionBelow.last_pair_ratios_mem
    {s a b : ℝ} {x : List ℝ} {k : ℕ}
    (hregion : UpperRosserLogRegionBelow s a b x)
    (hlen : x.length = 2 * (k + 1)) (ha : 0 < a) :
    x[2 * k + 1] / a ∈ Set.Ioo (1 : ℝ) 3 ∧
      x[2 * k] / a ∈ Set.Ioo (x[2 * k + 1] / a)
        ((x[2 * k + 1] / a + 3) / 2) := by
  have hiEven : 2 * k < x.length := by omega
  have hiOdd : 2 * k + 1 < x.length := by omega
  have hOddMem : x[2 * k + 1] ∈ x := List.getElem_mem hiOdd
  have haOdd : a < x[2 * k + 1] := (hregion.2 _ hOddMem).1
  have hOddEven : x[2 * k + 1] < x[2 * k] := by
    let i : Fin x.length := ⟨2 * k, hiEven⟩
    let j : Fin x.length := ⟨2 * k + 1, hiOdd⟩
    have hij : i < j := by simp [i, j]
    simpa [i, j] using hregion.1.1 hij
  have hsuffix := hregion.1.last_pair_lt_terminal hlen
  have hOneOdd : (1 : ℝ) < x[2 * k + 1] / a :=
    (lt_div_iff₀ ha).2 (by simpa using haOdd)
  have hOddRatioEven : x[2 * k + 1] / a < x[2 * k] / a :=
    (div_lt_div_iff_of_pos_right ha).2 hOddEven
  have hscaled : (2 * x[2 * k]) / a <
      (x[2 * k + 1] + 3 * a) / a :=
    (div_lt_div_iff_of_pos_right ha).2 hsuffix
  have heq : (x[2 * k + 1] + 3 * a) / a =
      x[2 * k + 1] / a + 3 := by
    field_simp [ha.ne']
  have heveneq : (2 * x[2 * k]) / a =
      2 * (x[2 * k] / a) := by ring
  rw [heq, heveneq] at hscaled
  have hEvenUpper :
      x[2 * k] / a < (x[2 * k + 1] / a + 3) / 2 := by
    linarith
  have hOddThree : x[2 * k + 1] / a < 3 := by linarith
  exact ⟨⟨hOneOdd, hOddThree⟩, hOddRatioEven, hEvenUpper⟩

/-- Alternating cubic-prefix inequalities contract the unused logarithmic
budget by a factor of three after each pair of decreasing coordinates. -/
theorem sum_add_geometric_le_of_sortedGT_even_prefix
    {s : ℝ} {x : List ℝ} {k : ℕ} (hs : 0 ≤ s)
    (hlen : x.length = 2 * k) (hsorted : x.SortedGT)
    (hprefix : ∀ i (hi : i < x.length), Even i →
      (x.take i).sum + 3 * x[i] ≤ s) :
    x.sum + s / 3 ^ k ≤ s := by
  induction k generalizing s x with
  | zero =>
      have hx : x = [] := by simpa using hlen
      subst x
      simp
  | succ k ih =>
      cases x with
      | nil => simp at hlen
      | cons x₀ tail =>
        cases tail with
        | nil => simp at hlen; omega
        | cons x₁ xs =>
          have hlenxs : xs.length = 2 * k := by
            simp only [List.length_cons] at hlen
            omega
          have h01 : x₁ ≤ x₀ := by
            let i : Fin (x₀ :: x₁ :: xs).length := ⟨0, by simp⟩
            let j : Fin (x₀ :: x₁ :: xs).length := ⟨1, by simp⟩
            have hij : i < j := by simp [i, j]
            have hstrict := hsorted hij
            change x₁ < x₀ at hstrict
            exact hstrict.le
          have hx₀ : 3 * x₀ ≤ s := by
            have h := hprefix 0 (by simp) (by simp)
            norm_num at h
            exact h
          let s' := s - x₀ - x₁
          have hs' : 0 ≤ s' := by
            dsimp [s']
            linarith
          have hsorted' : xs.SortedGT := by
            intro i j hij
            have h :
                (x₀ :: x₁ :: xs).get
                    ⟨j.val + 2, by simp [hlenxs]; omega⟩ <
                  (x₀ :: x₁ :: xs).get
                    ⟨i.val + 2, by simp [hlenxs]; omega⟩ :=
              hsorted (by simp; omega)
            simpa using h
          have hprefix' : ∀ i (hi : i < xs.length), Even i →
              (xs.take i).sum + 3 * xs[i] ≤ s' := by
            intro i hi heven
            have horig := hprefix (i + 2) (by simp [hlenxs]; omega)
              (heven.add (by simp))
            change x₀ + (x₁ + (xs.take i).sum) + 3 * xs[i] ≤ s at horig
            dsimp [s']
            linarith
          have htail := ih hs' hlenxs hsorted' hprefix'
          have hsdiv : s / 3 ^ (k + 1) ≤ s' / 3 ^ k := by
            have hpow : (0 : ℝ) < 3 ^ k := by positivity
            rw [pow_succ]
            calc
              s / (3 ^ k * 3) = (s / 3) / 3 ^ k := by ring
              _ ≤ s' / 3 ^ k := (div_le_div_iff_of_pos_right hpow).2 (by
                dsimp [s']
                linarith)
          simp only [List.sum_cons]
          linarith

/-- A depth-`2k` upper Rosser region leaves at least `s / 3^k` of the
logarithmic budget unused by its selected coordinates. -/
theorem UpperRosserLogRegion.sum_add_geometric_le
    {s a : ℝ} {x : List ℝ} {k : ℕ}
    (hregion : UpperRosserLogRegion s a x) (hs : 0 ≤ s)
    (hlen : x.length = 2 * k) :
    x.sum + s / 3 ^ k ≤ s :=
  sum_add_geometric_le_of_sortedGT_even_prefix hs hlen hregion.1
    hregion.2.2.2.1

/-- The terminal boundary coordinate of a depth-`2k` Rosser region stays
uniformly away from zero. -/
theorem UpperRosserLogRegion.outer_lower
    {s a : ℝ} {x : List ℝ} {k : ℕ}
    (hregion : UpperRosserLogRegion s a x) (hs : 0 ≤ s)
    (hlen : x.length = 2 * k) :
    s / 3 ^ (k + 1) < a := by
  have hsum := hregion.sum_add_geometric_le hs hlen
  have hgap : s / 3 ^ k < 3 * a := by linarith [hregion.2.2.2.2]
  rw [pow_succ]
  calc
    s / (3 ^ k * 3) = (s / 3 ^ k) / 3 := by ring
    _ < (3 * a) / 3 := div_lt_div_of_pos_right hgap (by norm_num)
    _ = a := by ring

/-- On the fundamental-lemma range, the depth-`2k` outer coordinate is bounded
below by a constant depending only on the fixed depth. -/
theorem UpperRosserLogRegion.outer_lower_of_three_halves_le
    {s a : ℝ} {x : List ℝ} {k : ℕ}
    (hregion : UpperRosserLogRegion s a x) (hs : 3 / 2 ≤ s)
    (hlen : x.length = 2 * k) :
    1 / (2 * 3 ^ k) < a := by
  have ha := hregion.outer_lower (by linarith) hlen
  have hpow : (0 : ℝ) < 3 ^ (k + 1) := by positivity
  calc
    1 / (2 * 3 ^ k) = (3 / 2 : ℝ) / 3 ^ (k + 1) := by
      rw [pow_succ]
      field_simp
    _ ≤ s / 3 ^ (k + 1) := (div_le_div_iff_of_pos_right hpow).2 hs
    _ < a := ha

/-- The reverse-chain integral operator obtained by adjoining one ordered pair.
Here `r` is the suffix-plus-terminal budget divided by the current terminal
coordinate, `y` is the smaller new coordinate, and `x` the larger one.  The
upper face `2x < y + r` is exactly an even-prefix Rosser inequality. -/
noncomputable def upperRosserAlternatingPairTransform
    (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ y in Set.Ioo 1 r, y⁻¹ *
    ∫ x in Set.Ioo y ((y + r) / 2),
      x⁻¹ * F ((r + y + x) / x)

/-- The quadratic reverse-pair kernel normalized by the current state. -/
noncomputable def upperRosserAlternatingPairNormalizedKernel
    (r y x : ℝ) : ℝ :=
  ((r + y + x) / x) ^ 2 / r ^ 2

theorem upperRosserAlternatingPairNormalizedKernel_nonneg
    (r y x : ℝ) :
    0 ≤ upperRosserAlternatingPairNormalizedKernel r y x := by
  unfold upperRosserAlternatingPairNormalizedKernel
  positivity

/-- On a fixed ratio window, the normalized reverse-pair kernel has a bound
independent of the current state. -/
theorem upperRosserAlternatingPairNormalizedKernel_le_sq
    {r y x R : ℝ} (hr : 3 ≤ r) (hR : 3 ≤ R)
    (hx : x ∈ Set.Icc (1 : ℝ) R) (hy : y ∈ Set.Icc (1 : ℝ) R) :
    upperRosserAlternatingPairNormalizedKernel r y x ≤ R ^ 2 := by
  have hrpos : 0 < r := by linarith
  have hxpos : 0 < x := by linarith [hx.1]
  have hRpos : 0 < R := by linarith
  have hnumpos : 0 < r + y + x := by linarith [hy.1, hx.1]
  have hnum : r + y + x ≤ R * r * x := by
    have hrr : r + 2 * R ≤ R * r := by nlinarith
    have hmul : R * r ≤ R * r * x := by nlinarith [hx.1]
    linarith [hy.2, hx.2]
  have hratio : 0 ≤ (r + y + x) / x / r := by positivity
  have hratioLe : (r + y + x) / x / r ≤ R := by
    rw [div_le_iff₀ hrpos, div_le_iff₀ hxpos]
    nlinarith [hnum]
  unfold upperRosserAlternatingPairNormalizedKernel
  rw [show ((r + y + x) / x) ^ 2 / r ^ 2 =
      ((r + y + x) / x / r) ^ 2 by field_simp]
  exact pow_le_pow_left₀ hratio hratioLe 2

/-- The normalized reverse-pair kernel is uniformly Lipschitz in its larger
coordinate on a fixed ratio window. -/
theorem abs_upperRosserAlternatingPairNormalizedKernel_sub_le
    {r y u v R : ℝ} (hr : 3 ≤ r) (hR : 3 ≤ R)
    (hu : u ∈ Set.Icc (1 : ℝ) R) (hv : v ∈ Set.Icc (1 : ℝ) R)
    (hy : y ∈ Set.Icc (1 : ℝ) R) :
    |upperRosserAlternatingPairNormalizedKernel r y u -
        upperRosserAlternatingPairNormalizedKernel r y v| ≤
      3 * R ^ 2 * |u - v| := by
  have hrpos : 0 < r := by linarith
  have hupos : 0 < u := by linarith [hu.1]
  have hvpos : 0 < v := by linarith [hv.1]
  have hRpos : 0 < R := by linarith
  let A := r + y
  have hApos : 0 < A := by
    dsimp [A]
    linarith [hy.1]
  have hRminus : 0 ≤ R - 1 := by linarith
  have hprod : 3 * (R - 1) ≤ r * (R - 1) :=
    mul_le_mul_of_nonneg_right hr hRminus
  have hAr : A / r ≤ R := by
    rw [div_le_iff₀ hrpos]
    dsimp [A]
    nlinarith [hy.2]
  have hau : 0 < 1 + A / u := by positivity
  have hav : 0 < 1 + A / v := by positivity
  have hsum :
      (1 + A / u + (1 + A / v)) / r ≤ 3 * R := by
    rw [div_le_iff₀ hrpos]
    have hAu : A / u ≤ A := by
      rw [div_le_iff₀ hupos]
      nlinarith [hu.1]
    have hAv : A / v ≤ A := by
      rw [div_le_iff₀ hvpos]
      nlinarith [hv.1]
    have hAr' : A ≤ R * r := by
      rw [← div_le_iff₀ hrpos]
      exact hAr
    nlinarith
  have hinv : |u⁻¹ - v⁻¹| ≤ |u - v| := by
    rw [inv_sub_inv hupos.ne' hvpos.ne', abs_div, abs_mul,
      abs_of_pos hupos, abs_of_pos hvpos]
    have huv : 1 ≤ u * v := by nlinarith [hu.1, hv.1]
    have huvpos : 0 < u * v := mul_pos hupos hvpos
    have hden : 1 / (u * v) ≤ 1 := (div_le_one huvpos).2 huv
    rw [abs_sub_comm]
    calc
      |u - v| / (u * v) = |u - v| * (1 / (u * v)) := by ring
      _ ≤ |u - v| * 1 :=
        mul_le_mul_of_nonneg_left hden (abs_nonneg _)
      _ = |u - v| := by ring
  have hfactor :
      (A / r) * ((1 + A / u + (1 + A / v)) / r) ≤
        3 * R ^ 2 := by
    calc
      (A / r) * ((1 + A / u + (1 + A / v)) / r) ≤
          R * (3 * R) :=
        mul_le_mul hAr hsum (by positivity) hRpos.le
      _ = 3 * R ^ 2 := by ring
  have hfactorNonneg : 0 ≤
      (A / r) * ((1 + A / u + (1 + A / v)) / r) := by
    positivity
  rw [show upperRosserAlternatingPairNormalizedKernel r y u =
        (1 + A / u) ^ 2 / r ^ 2 by
      dsimp [upperRosserAlternatingPairNormalizedKernel, A]
      congr 2
      field_simp
      ring,
    show upperRosserAlternatingPairNormalizedKernel r y v =
        (1 + A / v) ^ 2 / r ^ 2 by
      dsimp [upperRosserAlternatingPairNormalizedKernel, A]
      congr 2
      field_simp
      ring]
  have halg :
      (1 + A / u) ^ 2 / r ^ 2 - (1 + A / v) ^ 2 / r ^ 2 =
        ((A / r) * ((1 + A / u + (1 + A / v)) / r)) *
          (u⁻¹ - v⁻¹) := by
    field_simp [hrpos.ne', hupos.ne', hvpos.ne']
    ring
  rw [halg, abs_mul, abs_of_nonneg hfactorNonneg]
  exact (mul_le_mul_of_nonneg_left hinv hfactorNonneg).trans
    (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _))

/-- The reverse-chain state remains in the invariant range `r > 3` after one
pair is adjoined. -/
theorem upperRosserAlternatingPair_nextRatio_gt_three
    {r y x : ℝ} (hy : y ∈ Set.Ioo (1 : ℝ) r)
    (hx : x ∈ Set.Ioo y ((y + r) / 2)) :
    3 < (r + y + x) / x := by
  have hxpos : 0 < x := (by linarith [hy.1, hx.1])
  apply (lt_div_iff₀ hxpos).2
  linarith [hx.2]

theorem integral_upperRosserAlternatingPair_quadratic_inner
    {r y : ℝ} (hy : 0 < y) (hyr : y ≤ r) :
    (∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * ((r + y + x) / x) ^ 2) =
      r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
        Real.log ((y + r) / (2 * y)) := by
  let u : ℝ := (y + r) / 2
  have hyu : y ≤ u := by
    dsimp [u]
    linarith
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hyu]
  have hzero : (0 : ℝ) ∉ Set.uIcc y u := by
    rw [Set.uIcc_of_le hyu]
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hy)
  have hne : ∀ x ∈ Set.uIcc y u, x ≠ 0 := by
    rw [Set.uIcc_of_le hyu]
    intro x hx
    exact ne_of_gt (hy.trans_le hx.1)
  have hInt3 :
      IntervalIntegrable (fun x : ℝ => x ^ (-3 : ℤ))
        MeasureTheory.volume y u :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hInt2 :
      IntervalIntegrable (fun x : ℝ => x ^ (-2 : ℤ))
        MeasureTheory.volume y u :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hInt1 :
      IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume y u :=
    intervalIntegral.intervalIntegrable_inv hne continuousOn_id
  have hI3 := integral_zpow (a := y) (b := u) (n := (-3 : ℤ))
    (Or.inr ⟨by norm_num, hzero⟩)
  have hI2 := integral_zpow (a := y) (b := u) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hzero⟩)
  have hI1 : (∫ x : ℝ in y..u, x⁻¹) = Real.log (u / y) :=
    integral_inv hzero
  have hsplit :
      (∫ x : ℝ in y..u, (r + y) ^ 2 * x ^ (-3 : ℤ) +
          2 * (r + y) * x ^ (-2 : ℤ) + x⁻¹) =
        (r + y) ^ 2 * (∫ x : ℝ in y..u, x ^ (-3 : ℤ)) +
          2 * (r + y) * (∫ x : ℝ in y..u, x ^ (-2 : ℤ)) +
          (∫ x : ℝ in y..u, x⁻¹) := by
    rw [intervalIntegral.integral_add
      ((hInt3.const_mul _).add (hInt2.const_mul _)) hInt1,
      intervalIntegral.integral_add (hInt3.const_mul _) (hInt2.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  calc
    (∫ x : ℝ in y..u, x⁻¹ * ((r + y + x) / x) ^ 2) =
        ∫ x : ℝ in y..u, (r + y) ^ 2 * x ^ (-3 : ℤ) +
          2 * (r + y) * x ^ (-2 : ℤ) + x⁻¹ := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx0 : x ≠ 0 := hne x hx
            simp [zpow_neg]
            field_simp
            ring
    _ = (r + y) ^ 2 * (∫ x : ℝ in y..u, x ^ (-3 : ℤ)) +
          2 * (r + y) * (∫ x : ℝ in y..u, x ^ (-2 : ℤ)) +
          (∫ x : ℝ in y..u, x⁻¹) := hsplit
    _ = r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
          Real.log ((y + r) / (2 * y)) := by
            rw [hI3, hI2, hI1]
            dsimp [u]
            simp only [zpow_neg, zpow_one]
            norm_num
            have hyr0 : y + r ≠ 0 := by linarith
            field_simp [hy.ne', hyr0]
            ring

/-- The reverse-pair operator is linear in a constant coefficient. -/
theorem upperRosserAlternatingPairTransform_const_mul
    (c r : ℝ) (F : ℝ → ℝ) :
    upperRosserAlternatingPairTransform (fun t => c * F t) r =
      c * upperRosserAlternatingPairTransform F r := by
  unfold upperRosserAlternatingPairTransform
  calc
    (∫ y in Set.Ioo 1 r, y⁻¹ *
      ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * (c * F ((r + y + x) / x))) =
      ∫ y in Set.Ioo 1 r, y⁻¹ *
        (c * ∫ x in Set.Ioo y ((y + r) / 2),
          x⁻¹ * F ((r + y + x) / x)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            congr 1
            rw [← MeasureTheory.integral_const_mul]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
    _ = c * ∫ y in Set.Ioo 1 r, y⁻¹ *
        ∫ x in Set.Ioo y ((y + r) / 2),
          x⁻¹ * F ((r + y + x) / x) := by
            rw [← MeasureTheory.integral_const_mul]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            ring

/-- One reverse Rosser pair contracts the quadratic suffix envelope by a fixed
factor.  The estimate is genuinely geometric: its triangular integration face
is `2x < y + r`, the inequality contributed by the corresponding even prefix. -/
theorem upperRosserAlternatingPairTransform_quadratic_le
    {r : ℝ} (hr : 3 ≤ r) :
    upperRosserAlternatingPairTransform (fun t => t ^ 2) r ≤
      (4 / 5 : ℝ) * r ^ 2 := by
  have h1r : (1 : ℝ) ≤ r := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc 1 r := by
    rw [Set.uIcc_of_le h1r]
    norm_num
  have hne : ∀ y ∈ Set.uIcc (1 : ℝ) r, y ≠ 0 := by
    rw [Set.uIcc_of_le h1r]
    intro y hy
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hy.1)
  let F : ℝ → ℝ := fun y => y⁻¹ *
    (r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
      Real.log ((y + r) / (2 * y)))
  let G : ℝ → ℝ := fun y =>
    r ^ 2 / 2 * y ^ (-3 : ℤ) +
      (7 * r / 2) * y ^ (-2 : ℤ) - 4 * y⁻¹
  have hFcont : ContinuousOn F (Set.Icc 1 r) := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hyr0 : y + r ≠ 0 := by linarith [hy.1]
    have hden0 : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy0
    have hden2 : 2 * y ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero _ hy0)
    have hratio0 : (y + r) / (2 * y) ≠ 0 :=
      div_ne_zero hyr0 hden0
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop
  have hFint : IntervalIntegrable F MeasureTheory.volume 1 r := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le h1r] using hFcont
  have hInt3 :
      IntervalIntegrable (fun y : ℝ => y ^ (-3 : ℤ))
        MeasureTheory.volume 1 r :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hInt2 :
      IntervalIntegrable (fun y : ℝ => y ^ (-2 : ℤ))
        MeasureTheory.volume 1 r :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hInt1 :
      IntervalIntegrable (fun y : ℝ => y⁻¹) MeasureTheory.volume 1 r :=
    intervalIntegral.intervalIntegrable_inv hne continuousOn_id
  have hGint : IntervalIntegrable G MeasureTheory.volume 1 r := by
    exact ((hInt3.const_mul _).add (hInt2.const_mul _)).sub
      (hInt1.const_mul _)
  have hpoint : ∀ y ∈ Set.Icc (1 : ℝ) r, F y ≤ G y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
    have hr0 : 0 < r := hy0.trans_le hy.2
    have hratioPos : 0 < (y + r) / (2 * y) :=
      div_pos (add_pos hy0 hr0) (by positivity)
    have hlog := Real.log_le_sub_one_of_pos hratioPos
    have hratio :
        (y + r) / (2 * y) - 1 = (r - y) / (2 * y) := by
      field_simp [hy0.ne']
      ring
    rw [hratio] at hlog
    have hyinv : 0 ≤ y⁻¹ := inv_nonneg.mpr hy0.le
    dsimp [F, G]
    simp only [zpow_neg]
    calc
      y⁻¹ * (r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
          Real.log ((y + r) / (2 * y))) ≤
        y⁻¹ * (r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
          (r - y) / (2 * y)) :=
            mul_le_mul_of_nonneg_left (by linarith) hyinv
      _ = r ^ 2 / 2 * (y ^ 3)⁻¹ +
          (7 * r / 2) * (y ^ 2)⁻¹ - 4 * y⁻¹ := by
        field_simp [hy0.ne']
        ring
  have houter : (∫ y : ℝ in 1..r, G y) =
      r ^ 2 / 4 + 7 * r / 2 - 15 / 4 - 4 * Real.log r := by
    have hI3 := integral_zpow (a := (1 : ℝ)) (b := r)
      (n := (-3 : ℤ)) (Or.inr ⟨by norm_num, hzero⟩)
    have hI2 := integral_zpow (a := (1 : ℝ)) (b := r)
      (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hzero⟩)
    have hI1 : (∫ y : ℝ in 1..r, y⁻¹) = Real.log r := by
      simpa using (integral_inv hzero)
    dsimp [G]
    rw [intervalIntegral.integral_sub
        ((hInt3.const_mul _).add (hInt2.const_mul _))
          (hInt1.const_mul _),
      intervalIntegral.integral_add (hInt3.const_mul _)
        (hInt2.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      hI3, hI2, hI1]
    norm_num
    have hr0 : r ≠ 0 := by linarith
    field_simp [hr0]
    ring
  have hlogLower : (69 / 100 : ℝ) ≤ Real.log r := by
    have htwoPos : (2 : ℝ) ∈ Set.Ioi 0 := by norm_num
    have hrPos : r ∈ Set.Ioi (0 : ℝ) := by
      change 0 < r
      linarith
    have htwoLe : (2 : ℝ) ≤ r := by linarith
    have hlogTwoLe : Real.log 2 ≤ Real.log r :=
      Real.strictMonoOn_log.monotoneOn htwoPos hrPos htwoLe
    exact (show (69 / 100 : ℝ) ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]).trans hlogTwoLe
  unfold upperRosserAlternatingPairTransform
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le h1r]
  calc
    (∫ y : ℝ in 1..r, y⁻¹ *
        ∫ x in Set.Ioo y ((y + r) / 2),
          x⁻¹ * ((r + y + x) / x) ^ 2) =
      ∫ y : ℝ in 1..r, F y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le h1r] at hy
        dsimp [F]
        rw [integral_upperRosserAlternatingPair_quadratic_inner
          (by linarith [hy.1]) hy.2]
    _ ≤ ∫ y : ℝ in 1..r, G y :=
      intervalIntegral.integral_mono_on h1r hFint hGint hpoint
    _ = r ^ 2 / 4 + 7 * r / 2 - 15 / 4 - 4 * Real.log r := houter
    _ ≤ (4 / 5 : ℝ) * r ^ 2 := by
      nlinarith [sq_nonneg (11 * r - 35)]

/-- The normalized quadratic kernel has total reverse-pair mass at most `4 / 5`.
This is the scale-free form used in the discrete contraction argument. -/
theorem integral_upperRosserAlternatingPairNormalizedKernel_le
    {r : ℝ} (hr : 3 ≤ r) :
    (∫ y in Set.Ioo 1 r, y⁻¹ *
      ∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
        upperRosserAlternatingPairNormalizedKernel r y x) ≤
      (4 / 5 : ℝ) := by
  have hrpos : 0 < r := by linarith
  have heq :
      (∫ y in Set.Ioo 1 r, y⁻¹ *
        ∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
          upperRosserAlternatingPairNormalizedKernel r y x) =
        upperRosserAlternatingPairTransform (fun t => t ^ 2) r / r ^ 2 := by
    unfold upperRosserAlternatingPairTransform
    rw [← MeasureTheory.integral_div]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    have hinner :
        (∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
            upperRosserAlternatingPairNormalizedKernel r y x) =
          (∫ x in Set.Ioo y ((y + r) / 2),
            x⁻¹ * ((r + y + x) / x) ^ 2) / r ^ 2 := by
      rw [← MeasureTheory.integral_div]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      unfold upperRosserAlternatingPairNormalizedKernel
      ring
    rw [hinner]
    ring
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hrpos)).2
  exact upperRosserAlternatingPairTransform_quadratic_le hr

/-- Measurability of the inner integral in the reverse-pair operator. -/
theorem stronglyMeasurable_upperRosserAlternatingPair_inner
    (F : ℝ → ℝ) (hF : MeasureTheory.StronglyMeasurable F) (r : ℝ) :
    MeasureTheory.StronglyMeasurable
      (fun y => ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * F ((r + y + x) / x)) := by
  let innerSet : Set (ℝ × ℝ) :=
    {p | p.1 < p.2 ∧ p.2 < (p.1 + r) / 2}
  let innerIntegrand : ℝ × ℝ → ℝ := fun p =>
    innerSet.indicator (fun p => p.2⁻¹ *
      F ((r + p.1 + p.2) / p.2)) p
  have hmap :
      Measurable (fun p : ℝ × ℝ => (r + p.1 + p.2) / p.2) := by
    fun_prop
  have hinnerSet : MeasurableSet innerSet := by
    apply (measurableSet_lt measurable_fst measurable_snd).inter
    exact measurableSet_lt measurable_snd
      ((measurable_fst.add_const r).div_const 2)
  have hinnerIntegrand :
      MeasureTheory.StronglyMeasurable innerIntegrand := by
    apply MeasureTheory.StronglyMeasurable.indicator
    · exact measurable_snd.inv.stronglyMeasurable.mul
        (hF.comp_measurable hmap)
    · exact hinnerSet
  have hraw :=
    hinnerIntegrand.integral_prod_right' (ν := MeasureTheory.volume)
  convert hraw using 1
  funext y
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
  rfl

private theorem integrableOn_upperRosserAlternatingPair_quadratic_inner
    {r y : ℝ} (hy : 0 < y) (hyr : y ≤ r) :
    MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * ((r + y + x) / x) ^ 2)
      (Set.Ioo y ((y + r) / 2)) := by
  have hyu : y ≤ (y + r) / 2 := by linarith
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hyu]
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hyu]
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  apply ContinuousAt.continuousWithinAt
  fun_prop

private theorem integrableOn_upperRosserAlternatingPair_quadratic_outer
    {r : ℝ} (hr : 3 ≤ r) :
    MeasureTheory.IntegrableOn
      (fun y => y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * ((r + y + x) / x) ^ 2) (Set.Ioo 1 r) := by
  have h1r : (1 : ℝ) ≤ r := by linarith
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le h1r]
  let F : ℝ → ℝ := fun y => y⁻¹ *
    (r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
      Real.log ((y + r) / (2 * y)))
  have hFcont : ContinuousOn F (Set.Icc 1 r) := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hyr0 : y + r ≠ 0 := by linarith [hy.1]
    have hden0 : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy0
    have hden2 : 2 * y ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero _ hy0)
    have hratio0 : (y + r) / (2 * y) ≠ 0 :=
      div_ne_zero hyr0 hden0
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop
  have hFint : IntervalIntegrable F MeasureTheory.volume 1 r := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le h1r] using hFcont
  apply hFint.congr
  intro y hy
  rw [Set.uIoc_of_le h1r] at hy
  dsimp [F]
  rw [integral_upperRosserAlternatingPair_quadratic_inner
    (by linarith [hy.1]) hy.2]

/-- Monotonicity of one reverse-pair step against a quadratic envelope.  The
hypotheses are pointwise only on the invariant range `t ≥ 3`; measurability is
enough to recover all required integrability from the quadratic majorant. -/
theorem upperRosserAlternatingPairTransform_le_const_mul_quadratic
    (F : ℝ → ℝ) {C r : ℝ} (hr : 3 ≤ r)
    (hFmeas : MeasureTheory.StronglyMeasurable F)
    (hFnonneg : ∀ t, 3 ≤ t → 0 ≤ F t)
    (hFle : ∀ t, 3 ≤ t → F t ≤ C * t ^ 2) :
    upperRosserAlternatingPairTransform F r ≤
      upperRosserAlternatingPairTransform (fun t => C * t ^ 2) r := by
  have hinnerMeas :=
    stronglyMeasurable_upperRosserAlternatingPair_inner F hFmeas r
  have houterFMeas : MeasureTheory.StronglyMeasurable
      (fun y => y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * F ((r + y + x) / x)) :=
    measurable_id.inv.stronglyMeasurable.mul hinnerMeas
  have hquadOuter :=
    integrableOn_upperRosserAlternatingPair_quadratic_outer hr
  have hmajorOuter : MeasureTheory.IntegrableOn
      (fun y => y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * (C * ((r + y + x) / x) ^ 2)) (Set.Ioo 1 r) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hquadOuter.const_mul C) ?_ measurableSet_Ioo
    intro y hy
    have hinner :
        (∫ x in Set.Ioo y ((y + r) / 2),
            x⁻¹ * (C * ((r + y + x) / x) ^ 2)) =
          C * ∫ x in Set.Ioo y ((y + r) / 2),
            x⁻¹ * ((r + y + x) / x) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring
    change C * (y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * ((r + y + x) / x) ^ 2) =
      y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * (C * ((r + y + x) / x) ^ 2)
    rw [hinner]
    ring
  have hinnerBound : ∀ y ∈ Set.Ioo (1 : ℝ) r,
      (∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * F ((r + y + x) / x)) ≤
      ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * (C * ((r + y + x) / x) ^ 2) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    let f : ℝ → ℝ := fun x => x⁻¹ * F ((r + y + x) / x)
    let g : ℝ → ℝ := fun x =>
      x⁻¹ * (C * ((r + y + x) / x) ^ 2)
    have hbaseInt :=
      integrableOn_upperRosserAlternatingPair_quadratic_inner hy0 hy.2.le
    have hgInt :
        MeasureTheory.IntegrableOn g (Set.Ioo y ((y + r) / 2)) := by
      refine MeasureTheory.IntegrableOn.congr_fun
        (hbaseInt.const_mul C) ?_ measurableSet_Ioo
      intro x hx
      dsimp [g]
      ring
    have hfMeas : MeasureTheory.StronglyMeasurable f := by
      dsimp [f]
      exact measurable_id.inv.stronglyMeasurable.mul
        (hFmeas.comp_measurable (by fun_prop))
    have hfInt :
        MeasureTheory.IntegrableOn f (Set.Ioo y ((y + r) / 2)) := by
      apply hgInt.mono' hfMeas.aestronglyMeasurable.restrict
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      have ht := upperRosserAlternatingPair_nextRatio_gt_three hy hx
      have hx0 : 0 ≤ x⁻¹ :=
        inv_nonneg.mpr (by linarith [hy.1, hx.1])
      have hfn := hFnonneg _ ht.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 hfn)]
      exact mul_le_mul_of_nonneg_left (hFle _ ht.le) hx0
    apply MeasureTheory.setIntegral_mono_on
      hfInt hgInt measurableSet_Ioo
    intro x hx
    have ht := upperRosserAlternatingPair_nextRatio_gt_three hy hx
    exact mul_le_mul_of_nonneg_left (hFle _ ht.le)
      (inv_nonneg.mpr (by linarith [hy.1, hx.1]))
  have houterNonneg : ∀ y ∈ Set.Ioo (1 : ℝ) r,
      0 ≤ y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * F ((r + y + x) / x) := by
    intro y hy
    apply mul_nonneg (inv_nonneg.mpr (by linarith [hy.1]))
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg
      (inv_nonneg.mpr (by linarith [hy.1, hx.1]))
      (hFnonneg _
        (upperRosserAlternatingPair_nextRatio_gt_three hy hx).le)
  have houterInt : MeasureTheory.IntegrableOn
      (fun y => y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2),
        x⁻¹ * F ((r + y + x) / x)) (Set.Ioo 1 r) := by
    apply hmajorOuter.mono'
      houterFMeas.aestronglyMeasurable.restrict
    filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (houterNonneg y hy)]
    exact mul_le_mul_of_nonneg_left (hinnerBound y hy)
      (inv_nonneg.mpr (by linarith [hy.1]))
  unfold upperRosserAlternatingPairTransform
  exact MeasureTheory.setIntegral_mono_on
    houterInt hmajorOuter measurableSet_Ioo
      (fun y hy => mul_le_mul_of_nonneg_left (hinnerBound y hy)
        (inv_nonneg.mpr (by linarith [hy.1])))

/-- The explicit geometric envelope for `k` reverse Rosser pairs. -/
noncomputable def upperRosserAlternatingPrefixMajorant
    (k : ℕ) (r : ℝ) : ℝ :=
  (4 / 5 : ℝ) ^ k * r ^ 2

/-- Applying one constrained reverse-pair integral to the depth-`k` envelope
lands below the depth-`k+1` envelope. -/
theorem upperRosserAlternatingPairTransform_majorant_le
    (k : ℕ) {r : ℝ} (hr : 3 ≤ r) :
    upperRosserAlternatingPairTransform
        (upperRosserAlternatingPrefixMajorant k) r ≤
      upperRosserAlternatingPrefixMajorant (k + 1) r := by
  change upperRosserAlternatingPairTransform
      (fun t => (4 / 5 : ℝ) ^ k * t ^ 2) r ≤ _
  rw [upperRosserAlternatingPairTransform_const_mul]
  calc
    (4 / 5 : ℝ) ^ k *
        upperRosserAlternatingPairTransform (fun t => t ^ 2) r ≤
      (4 / 5 : ℝ) ^ k * ((4 / 5 : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_left
          (upperRosserAlternatingPairTransform_quadratic_le hr) (by positivity)
    _ = upperRosserAlternatingPrefixMajorant (k + 1) r := by
      simp [upperRosserAlternatingPrefixMajorant, pow_succ]
      ring

/-- Scale-free volume of `k` reverse-built Rosser pairs.  Starting from terminal
state `r = 3`, each recursion imposes decreasing order and the next even-prefix
constraint instead of integrating over all unordered coordinates. -/
noncomputable def upperRosserAlternatingPrefixVolume : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, r =>
      upperRosserAlternatingPairTransform
        (upperRosserAlternatingPrefixVolume k) r

theorem stronglyMeasurable_upperRosserAlternatingPrefixVolume (k : ℕ) :
    MeasureTheory.StronglyMeasurable
      (upperRosserAlternatingPrefixVolume k) := by
  induction k with
  | zero => exact measurable_const.stronglyMeasurable
  | succ k ih =>
      change MeasureTheory.StronglyMeasurable
        (fun r => upperRosserAlternatingPairTransform
          (upperRosserAlternatingPrefixVolume k) r)
      let innerSet : Set ((ℝ × ℝ) × ℝ) :=
        {p | p.1.2 < p.2 ∧ p.2 < (p.1.2 + p.1.1) / 2}
      let innerIntegrand : ((ℝ × ℝ) × ℝ) → ℝ := fun p =>
        innerSet.indicator (fun p => p.2⁻¹ *
          upperRosserAlternatingPrefixVolume k
            ((p.1.1 + p.1.2 + p.2) / p.2)) p
      have hmap : Measurable (fun p : ((ℝ × ℝ) × ℝ) =>
          (p.1.1 + p.1.2 + p.2) / p.2) := by
        fun_prop
      have hinnerSet : MeasurableSet innerSet := by
        apply (measurableSet_lt
          (measurable_snd.comp measurable_fst) measurable_snd).inter
        exact measurableSet_lt measurable_snd
          (((measurable_snd.comp measurable_fst).add
            (measurable_fst.comp measurable_fst)).div_const 2)
      have hinnerIntegrand :
          MeasureTheory.StronglyMeasurable innerIntegrand := by
        apply MeasureTheory.StronglyMeasurable.indicator
        · exact measurable_snd.inv.stronglyMeasurable.mul
            (ih.comp_measurable hmap)
        · exact hinnerSet
      have hinnerRaw :=
        hinnerIntegrand.integral_prod_right' (ν := MeasureTheory.volume)
      have hinner : MeasureTheory.StronglyMeasurable
          (fun p : ℝ × ℝ =>
            ∫ x in Set.Ioo p.2 ((p.2 + p.1) / 2),
              x⁻¹ * upperRosserAlternatingPrefixVolume k
                ((p.1 + p.2 + x) / x)) := by
        convert hinnerRaw using 1
        funext p
        rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
        rfl
      let outerSet : Set (ℝ × ℝ) :=
        {p | 1 < p.2 ∧ p.2 < p.1}
      let outerIntegrand : ℝ × ℝ → ℝ := fun p =>
        outerSet.indicator (fun p => p.2⁻¹ *
          (∫ x in Set.Ioo p.2 ((p.2 + p.1) / 2),
            x⁻¹ * upperRosserAlternatingPrefixVolume k
              ((p.1 + p.2 + x) / x))) p
      have houterSet : MeasurableSet outerSet := by
        exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_fst)
      have houterIntegrand :
          MeasureTheory.StronglyMeasurable outerIntegrand := by
        apply MeasureTheory.StronglyMeasurable.indicator
        · exact measurable_snd.inv.stronglyMeasurable.mul hinner
        · exact houterSet
      have houterRaw :=
        houterIntegrand.integral_prod_right' (ν := MeasureTheory.volume)
      unfold upperRosserAlternatingPairTransform
      convert houterRaw using 1
      funext r
      rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
      rfl

/-- The constrained reverse-chain volume is nonnegative throughout its
invariant range. -/
theorem upperRosserAlternatingPrefixVolume_nonneg
    (k : ℕ) {r : ℝ} (hr : 3 ≤ r) :
    0 ≤ upperRosserAlternatingPrefixVolume k r := by
  induction k generalizing r with
  | zero => simp [upperRosserAlternatingPrefixVolume]
  | succ k ih =>
      rw [upperRosserAlternatingPrefixVolume]
      unfold upperRosserAlternatingPairTransform
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with y hy
      apply mul_nonneg
        (inv_nonneg.mpr (by linarith [hy.1]))
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      apply mul_nonneg
        (inv_nonneg.mpr (by linarith [hy.1, hx.1]))
      exact ih (upperRosserAlternatingPair_nextRatio_gt_three hy hx).le

/-- Every constrained reverse-chain volume is bounded by the explicit
geometric envelope. -/
theorem upperRosserAlternatingPrefixVolume_le_majorant
    (k : ℕ) {r : ℝ} (hr : 3 ≤ r) :
    upperRosserAlternatingPrefixVolume k r ≤
      upperRosserAlternatingPrefixMajorant k r := by
  induction k generalizing r with
  | zero =>
      rw [upperRosserAlternatingPrefixVolume,
        upperRosserAlternatingPrefixMajorant, pow_zero, one_mul]
      nlinarith [sq_nonneg r]
  | succ k ih =>
      rw [upperRosserAlternatingPrefixVolume]
      calc
        upperRosserAlternatingPairTransform
            (upperRosserAlternatingPrefixVolume k) r ≤
          upperRosserAlternatingPairTransform
              (fun t => (4 / 5 : ℝ) ^ k * t ^ 2) r := by
            apply upperRosserAlternatingPairTransform_le_const_mul_quadratic
              (upperRosserAlternatingPrefixVolume k) hr
                (stronglyMeasurable_upperRosserAlternatingPrefixVolume k)
            · intro t ht
              exact upperRosserAlternatingPrefixVolume_nonneg k ht
            · intro t ht
              simpa [upperRosserAlternatingPrefixMajorant] using ih ht
        _ = upperRosserAlternatingPairTransform
              (upperRosserAlternatingPrefixMajorant k) r := by
            rfl
        _ ≤ upperRosserAlternatingPrefixMajorant (k + 1) r :=
          upperRosserAlternatingPairTransform_majorant_le k hr

/-- At the terminal state `r = 3`, the constrained reverse-chain envelopes form
a summable geometric series. -/
theorem summable_upperRosserAlternatingPrefixMajorant_three :
    Summable (fun k : ℕ => upperRosserAlternatingPrefixMajorant k 3) := by
  have hgeom : Summable (fun k : ℕ => (4 / 5 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have heq : (fun k : ℕ => upperRosserAlternatingPrefixMajorant k 3) =
      fun k => (9 : ℝ) * (4 / 5 : ℝ) ^ k := by
    funext k
    simp [upperRosserAlternatingPrefixMajorant]
    ring
  rw [heq]
  exact hgeom.mul_left 9

/-- The actual constrained reverse-chain volumes are summable at the terminal
state because they are termwise dominated by the geometric envelope. -/
theorem summable_upperRosserAlternatingPrefixVolume_three :
    Summable (fun k : ℕ => upperRosserAlternatingPrefixVolume k 3) :=
  Summable.of_nonneg_of_le
    (fun k => upperRosserAlternatingPrefixVolume_nonneg k (by norm_num))
    (fun k => upperRosserAlternatingPrefixVolume_le_majorant k (by norm_num))
    summable_upperRosserAlternatingPrefixMajorant_three

/-- Exact tail sum of the scale-free alternating-prefix majorant. -/
theorem tsum_upperRosserAlternatingPrefixMajorant_three_natAdd (L : ℕ) :
    (∑' j : ℕ, upperRosserAlternatingPrefixMajorant (L + j) 3) =
      45 * (4 / 5 : ℝ) ^ L := by
  rw [show
      (fun j : ℕ => upperRosserAlternatingPrefixMajorant (L + j) 3) =
        fun j => (9 * (4 / 5 : ℝ) ^ L) * (4 / 5 : ℝ) ^ j by
    funext j
    simp [upperRosserAlternatingPrefixMajorant, pow_add]
    ring]
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num
  ring

/-- Every finite aggregate beyond depth `L` is bounded by the same explicit
geometric tail, independently of its terminal depth. -/
theorem sum_range_upperRosserAlternatingPrefixMajorant_three_natAdd_le
    (L n : ℕ) :
    ∑ j ∈ Finset.range n,
        upperRosserAlternatingPrefixMajorant (L + j) 3 ≤
      45 * (4 / 5 : ℝ) ^ L := by
  have hsum :
      Summable (fun j : ℕ =>
        upperRosserAlternatingPrefixMajorant (L + j) 3) := by
    have hgeom : Summable (fun j : ℕ => (4 / 5 : ℝ) ^ j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [show
        (fun j : ℕ => upperRosserAlternatingPrefixMajorant (L + j) 3) =
          fun j => (9 * (4 / 5 : ℝ) ^ L) * (4 / 5 : ℝ) ^ j by
      funext j
      simp [upperRosserAlternatingPrefixMajorant, pow_add]
      ring]
    exact hgeom.mul_left _
  rw [← tsum_upperRosserAlternatingPrefixMajorant_three_natAdd L]
  exact hsum.sum_le_tsum (Finset.range n) (by
    intro j hj
    simp [upperRosserAlternatingPrefixMajorant]
    positivity)

/-- The volume of any finite block of constrained depths beyond `L` is at most
the explicit geometric tail `45 (4/5)^L`. -/
theorem sum_range_upperRosserAlternatingPrefixVolume_three_natAdd_le
    (L n : ℕ) :
    ∑ j ∈ Finset.range n,
        upperRosserAlternatingPrefixVolume (L + j) 3 ≤
      45 * (4 / 5 : ℝ) ^ L := by
  calc
    ∑ j ∈ Finset.range n,
        upperRosserAlternatingPrefixVolume (L + j) 3 ≤
      ∑ j ∈ Finset.range n,
        upperRosserAlternatingPrefixMajorant (L + j) 3 := by
          apply Finset.sum_le_sum
          intro j hj
          exact upperRosserAlternatingPrefixVolume_le_majorant
            (L + j) (by norm_num)
    _ ≤ 45 * (4 / 5 : ℝ) ^ L :=
      sum_range_upperRosserAlternatingPrefixMajorant_three_natAdd_le L n

/-- The aggregate alternating-prefix majorant has a uniform tail cutoff. -/
theorem exists_sum_range_upperRosserAlternatingPrefixMajorant_three_natAdd_lt
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ L : ℕ, ∀ n : ℕ,
      ∑ j ∈ Finset.range n,
          upperRosserAlternatingPrefixMajorant (L + j) 3 < ρ := by
  have hpow :
      Filter.Tendsto (fun L : ℕ => (4 / 5 : ℝ) ^ L)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled :
      Filter.Tendsto (fun L : ℕ => 45 * (4 / 5 : ℝ) ^ L)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow :
      Filter.Tendsto (fun L : ℕ => 45 * (4 / 5 : ℝ) ^ L)
        Filter.atTop (nhds ((45 : ℝ) * 0)))
  have hevent := hscaled.eventually (Iio_mem_nhds hρ)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨L, hL⟩ := hevent
  refine ⟨L, fun n => ?_⟩
  exact
    (sum_range_upperRosserAlternatingPrefixMajorant_three_natAdd_le L n).trans_lt
      (hL L le_rfl)

/-- Consequently, one depth cutoff makes every finite tail of the constrained
reverse-chain volumes smaller than a prescribed positive error. -/
theorem exists_sum_range_upperRosserAlternatingPrefixVolume_three_natAdd_lt
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ L : ℕ, ∀ n : ℕ,
      ∑ j ∈ Finset.range n,
          upperRosserAlternatingPrefixVolume (L + j) 3 < ρ := by
  obtain ⟨L, hL⟩ :=
    exists_sum_range_upperRosserAlternatingPrefixMajorant_three_natAdd_lt hρ
  refine ⟨L, fun n => ?_⟩
  calc
    ∑ j ∈ Finset.range n,
        upperRosserAlternatingPrefixVolume (L + j) 3 ≤
      ∑ j ∈ Finset.range n,
        upperRosserAlternatingPrefixMajorant (L + j) 3 := by
          apply Finset.sum_le_sum
          intro j hj
          exact upperRosserAlternatingPrefixVolume_le_majorant
            (L + j) (by norm_num)
    _ < ρ := hL n


end MathlibNt.SieveTheory.LinearSieve
