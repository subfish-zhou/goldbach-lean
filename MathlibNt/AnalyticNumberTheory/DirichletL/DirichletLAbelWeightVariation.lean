import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Total variation bounds for Dirichlet Abel weights

The bounds here are obtained from the real-interval fundamental theorem of calculus and
`intervalIntegral.norm_integral_le_integral_norm`.  In particular, no monotonicity assertion is
made about the complex-valued weights.
-/

open Complex Finset Set MeasureTheory

namespace DirichletLAbelWeightVariation

/-- The complex Dirichlet-series weight on a positive real variable. -/
noncomputable def cpowWeight (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (-s)

/-- Its real derivative, written in a form convenient for norm estimates. -/
noncomputable def cpowWeightDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (x : ℂ) ^ (-s - 1)

lemma hasDerivAt_cpowWeight (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cpowWeight s) (cpowWeightDeriv s x) x := by
  have h := (@HasDerivAt.cpow_const _ _ _ (-s) (hasDerivAt_id (x : ℂ))
    (Or.inl (by simpa [Complex.slitPlane] using hx))).comp_ofReal
  convert! h using 1 <;> simp [cpowWeight, cpowWeightDeriv] <;> ring

lemma norm_cpowWeightDeriv (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖cpowWeightDeriv s x‖ = ‖s‖ * x ^ (-s.re - 1) := by
  rw [cpowWeightDeriv, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- One discrete complex weight difference is bounded by the integral of the norm of its
real derivative. -/
lemma norm_cpowWeight_succ_sub_le_integral (s : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖s‖ * x ^ (-s.re - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hpos : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hkle] at hx
    exact hk0.trans_le hx.1
  have hder : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (cpowWeight s) (cpowWeightDeriv s x) x :=
    fun x hx => hasDerivAt_cpowWeight s (hpos x hx)
  have heq : cpowWeightDeriv s = fun x => (-s) * cpowWeight (s + 1) x := by
    funext x
    unfold cpowWeightDeriv cpowWeight
    rw [show -(s + 1) = -s - 1 by ring]
  have hcont : ContinuousOn (cpowWeightDeriv s) (uIcc (k : ℝ) (k + 1 : ℝ)) := by
    intro x hx
    rw [heq]
    exact (continuousAt_const.mul
      (hasDerivAt_cpowWeight (s + 1) (hpos x hx)).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (cpowWeightDeriv s) volume (k : ℝ) (k + 1 : ℝ) :=
    hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  calc
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ =
        ‖∫ x in (k : ℝ)..(k + 1 : ℝ), cpowWeightDeriv s x‖ := by rw [hFTC]
    _ ≤ ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖cpowWeightDeriv s x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hkle
    _ = ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖s‖ * x ^ (-s.re - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change ‖cpowWeightDeriv s x‖ = ‖s‖ * x ^ (-s.re - 1)
      exact norm_cpowWeightDeriv s (hpos x hx)

/-- Explicit one-step majorant. -/
lemma norm_cpowWeight_succ_sub_le (s : ℂ) (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      (‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - (k + 1 : ℝ) ^ (-s.re)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  calc
    ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
        ∫ x in (k : ℝ)..(k + 1 : ℝ), ‖s‖ * x ^ (-s.re - 1) :=
      norm_cpowWeight_succ_sub_le_integral s hk
    _ = ‖s‖ * (((k + 1 : ℝ) ^ (-s.re) - (k : ℝ) ^ (-s.re)) / (-s.re)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow]
      · congr 1
        ring
      · right
        constructor
        · linarith
        · rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ k)]
          exact fun h0 => (not_le_of_gt hk0) h0.1
    _ = (‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - (k + 1 : ℝ) ^ (-s.re)) := by
      field_simp
      <;> ring

/-- Strong finite telescoping estimate for the total variation of `k ↦ k⁻ˢ`. -/
lemma sum_norm_cpowWeight_sub_le_sub (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      (‖s‖ / s.re) * ((m : ℝ) ^ (-s.re) - (n : ℝ) ^ (-s.re)) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn]
      calc
        _ ≤ (‖s‖ / s.re) * ((m : ℝ) ^ (-s.re) - (n : ℝ) ^ (-s.re)) +
            (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - (n + 1 : ℝ) ^ (-s.re)) :=
          add_le_add ih (norm_cpowWeight_succ_sub_le s hs (hm.trans hmn))
        _ = _ := by
          norm_num [Nat.cast_add, Nat.cast_one, add_comm]
          ring

/-- Finite total variation, in the simple endpoint form used by Abel summation. -/
lemma sum_norm_cpowWeight_sub_le (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖cpowWeight s (k + 1) - cpowWeight s k‖ ≤
      (‖s‖ / s.re) * (m : ℝ) ^ (-s.re) := by
  refine (sum_norm_cpowWeight_sub_le_sub s hs hm hmn).trans ?_
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hn : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  nlinarith

/-- The shifted infinite total variation is summable. -/
lemma summable_norm_cpowWeight_sub (s : ℂ) (hs : 0 < s.re) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun j : ℕ => ‖cpowWeight s (m + j + 1) - cpowWeight s (m + j)‖) := by
  apply summable_of_sum_range_le (fun _ => norm_nonneg _)
  intro n
  simpa [sum_Ico_eq_sum_range] using
    sum_norm_cpowWeight_sub_le s hs hm (Nat.le_add_right m n)

/-- Explicit `tsum` bound for the infinite total variation. -/
lemma tsum_norm_cpowWeight_sub_le (s : ℂ) (hs : 0 < s.re) (m : ℕ) (hm : 1 ≤ m) :
    ∑' j : ℕ, ‖cpowWeight s (m + j + 1) - cpowWeight s (m + j)‖ ≤
      (‖s‖ / s.re) * (m : ℝ) ^ (-s.re) := by
  apply Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
  intro n
  simpa [sum_Ico_eq_sum_range] using
    sum_norm_cpowWeight_sub_le s hs hm (Nat.le_add_right m n)

/-- The derivative weight `-log(x) x⁻ˢ`, with the logarithm kept real on the positive axis. -/
noncomputable def logCpowWeight (s : ℂ) (x : ℝ) : ℂ :=
  -(Real.log x : ℂ) * cpowWeight s x

noncomputable def logCpowWeightDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (s * (Real.log x : ℂ) - 1) * (x : ℂ) ^ (-s - 1)

lemma hasDerivAt_logCpowWeight (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logCpowWeight s) (logCpowWeightDeriv s x) x := by
  have hlog : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x : ℂ)⁻¹) x := by
    simpa [Complex.ofReal_inv] using (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hpow := hasDerivAt_cpowWeight s hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hmul : (x⁻¹ : ℂ) * cpowWeight s x = (x : ℂ) ^ (-s - 1) := by
    rw [← Complex.cpow_neg_one]
    unfold cpowWeight
    rw [← Complex.cpow_add _ _ hxC]
    congr 1
    ring
  have hderiv :
      -((x : ℂ)⁻¹) * cpowWeight s x +
          (-(Real.log x : ℂ)) * cpowWeightDeriv s x =
        logCpowWeightDeriv s x := by
    change -((x : ℂ)⁻¹) * cpowWeight s x +
        (-(Real.log x : ℂ)) * ((-s) * (x : ℂ) ^ (-s - 1)) =
      (s * (Real.log x : ℂ) - 1) * (x : ℂ) ^ (-s - 1)
    rw [show -((x : ℂ)⁻¹) * cpowWeight s x =
      -(((x : ℂ)⁻¹) * cpowWeight s x) by ring, hmul]
    ring
  change HasDerivAt
    (fun y : ℝ => -(Real.log y : ℂ) * cpowWeight s y)
    (logCpowWeightDeriv s x) x
  rw [← hderiv]
  exact hlog.neg.mul hpow

lemma norm_logCpowWeightDeriv_le (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖logCpowWeightDeriv s x‖ ≤
      (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [logCpowWeightDeriv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [map_sub, map_mul, norm_real, norm_one, neg_re, sub_re, one_re]
  have hc : ‖s * (Real.log x : ℂ) - 1‖ ≤ ‖s‖ * Real.log x + 1 := by
    calc
      _ ≤ ‖s * (Real.log x : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ * Real.log x + 1 := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, norm_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx0.le _)

/-- Explicit primitive budget for the derivative-weight variation. -/
noncomputable def logVariationBudget (s : ℂ) (x : ℝ) : ℝ :=
  x ^ (-s.re) *
    (1 / s.re + ‖s‖ * (Real.log x / s.re + 1 / s.re ^ 2))

lemma hasDerivAt_logVariationBudget (s : ℂ) (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logVariationBudget s)
      (-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x := by
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := -s.re) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have ha : HasDerivAt
      (fun y : ℝ => 1 / s.re + ‖s‖ * (Real.log y / s.re + 1 / s.re ^ 2))
      (‖s‖ * (x⁻¹ / s.re)) x := by
    convert ((hl.div_const s.re).add_const (1 / s.re ^ 2)).const_mul ‖s‖ |>.const_add
      (1 / s.re) using 1 <;> ring
  have hxp : x * x ^ (-s.re - 1) = x ^ (-s.re) := by
    calc
      x * x ^ (-s.re - 1) = x ^ (-s.re - 1) * x := mul_comm _ _
      _ = x ^ (-s.re - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-s.re - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = x ^ (-s.re) := by ring_nf
  have hderiv :
      -s.re * x ^ (-s.re - 1) *
          (1 / s.re + ‖s‖ * (Real.log x / s.re + 1 / s.re ^ 2)) +
        x ^ (-s.re) * (‖s‖ * (x⁻¹ / s.re)) =
      -(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
    rw [← hxp]
    field_simp [hs.ne', hx.ne']
    ring
  change HasDerivAt
    (fun y : ℝ => y ^ (-s.re) *
      (1 / s.re + ‖s‖ * (Real.log y / s.re + 1 / s.re ^ 2)))
    (-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x
  rw [← hderiv]
  exact hp.mul ha

lemma norm_logCpowWeight_succ_sub_le (s : ℂ) (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖logCpowWeight s (k + 1) - logCpowWeight s k‖ ≤
      logVariationBudget s k - logVariationBudget s (k + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hpos : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hkle] at hx
    exact hk0.trans_le hx.1
  have hone : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ), 1 ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hkle] at hx
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact hk1.trans hx.1
  have hder : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (logCpowWeight s) (logCpowWeightDeriv s x) x :=
    fun x hx => hasDerivAt_logCpowWeight s (hpos x hx)
  have hint : IntervalIntegrable (logCpowWeightDeriv s) volume (k : ℝ) (k + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hlog := ((Real.hasDerivAt_log (hpos x hx).ne').ofReal_comp).continuousAt
    have hpow := (hasDerivAt_cpowWeight (s + 1) (hpos x hx)).continuousAt
    have heq : logCpowWeightDeriv s =
        fun y : ℝ => (s * (Real.log y : ℂ) - 1) * cpowWeight (s + 1) y := by
      funext y
      unfold logCpowWeightDeriv cpowWeight
      congr 1
      ring
    rw [heq]
    exact (((continuousAt_const.mul hlog).sub continuousAt_const).mul hpow).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hmajor :
      ‖∫ x in (k : ℝ)..(k + 1 : ℝ), logCpowWeightDeriv s x‖ ≤
        ∫ x in (k : ℝ)..(k + 1 : ℝ),
          (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hkle).trans ?_
    apply intervalIntegral.integral_mono_on hkle
    · exact hint.norm
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      have hx' : x ∈ uIcc (k : ℝ) (k + 1 : ℝ) := by
        rw [Set.uIcc_of_le hkle] at hx ⊢
        exact hx
      exact ((continuousAt_const.add (continuousAt_const.mul
        (Real.hasDerivAt_log (hpos x hx').ne').continuousAt)).mul
        (Real.hasDerivAt_rpow_const (Or.inl (hpos x hx').ne')).continuousAt).continuousWithinAt
    · intro x hx
      apply norm_logCpowWeightDeriv_le s
      apply hone x
      rwa [Set.uIcc_of_le hkle]
  have hprim :
      (∫ x in (k : ℝ)..(k + 1 : ℝ),
          (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) =
        logVariationBudget s k - logVariationBudget s (k + 1) := by
    have hd : ∀ x ∈ uIcc (k : ℝ) (k + 1 : ℝ),
        HasDerivAt (fun y => -logVariationBudget s y)
          ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) x := by
      intro x hx
      have hneg := (hasDerivAt_logVariationBudget s hs (hpos x hx)).neg
      have hderiv :
          (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) =
            -(-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) := by ring
      rw [hderiv]
      change HasDerivAt (-logVariationBudget s)
        (-(-(1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1))) x
      exact hneg
    have hi : IntervalIntegrable
        (fun x : ℝ => (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1))
        volume (k : ℝ) (k + 1 : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      exact ((continuousAt_const.add (continuousAt_const.mul
        (Real.hasDerivAt_log (hpos x hx).ne').continuousAt)).mul
        (Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')).continuousAt).continuousWithinAt
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi using 1 <;> ring
  rw [← hFTC]
  exact hmajor.trans_eq hprim

lemma sum_norm_logCpowWeight_sub_le_sub (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖logCpowWeight s (k + 1) - logCpowWeight s k‖ ≤
      logVariationBudget s m - logVariationBudget s n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn]
      calc
        _ ≤ (logVariationBudget s m - logVariationBudget s n) +
            (logVariationBudget s n - logVariationBudget s (n + 1)) :=
          add_le_add ih (norm_logCpowWeight_succ_sub_le s hs (hm.trans hmn))
        _ = _ := by
          norm_num [Nat.cast_add]

lemma sum_norm_logCpowWeight_sub_le (s : ℂ) (hs : 0 < s.re) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, ‖logCpowWeight s (k + 1) - logCpowWeight s k‖ ≤
      logVariationBudget s m := by
  refine (sum_norm_logCpowWeight_sub_le_sub s hs hm hmn).trans ?_
  have hn : 0 ≤ logVariationBudget s n := by
    unfold logVariationBudget
    positivity
  linarith

lemma summable_norm_logCpowWeight_sub (s : ℂ) (hs : 0 < s.re) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun j : ℕ =>
      ‖logCpowWeight s (m + j + 1) - logCpowWeight s (m + j)‖) := by
  apply summable_of_sum_range_le (fun _ => norm_nonneg _)
  intro n
  simpa [sum_Ico_eq_sum_range] using
    sum_norm_logCpowWeight_sub_le s hs hm (Nat.le_add_right m n)

lemma tsum_norm_logCpowWeight_sub_le (s : ℂ) (hs : 0 < s.re) (m : ℕ) (hm : 1 ≤ m) :
    ∑' j : ℕ, ‖logCpowWeight s (m + j + 1) - logCpowWeight s (m + j)‖ ≤
      (m : ℝ) ^ (-s.re) *
        (1 / s.re + ‖s‖ * (Real.log m / s.re + 1 / s.re ^ 2)) := by
  change (∑' j : ℕ, ‖logCpowWeight s (m + j + 1) - logCpowWeight s (m + j)‖) ≤
    logVariationBudget s m
  apply Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
  intro n
  simpa [sum_Ico_eq_sum_range] using
    sum_norm_logCpowWeight_sub_le s hs hm (Nat.le_add_right m n)

end DirichletLAbelWeightVariation
