import MathlibNt.SieveTheory.Switching.BoundaryChainIntegrals

/-!
# Logarithmic kernel bounds and residual errors

Quantitative continuity bounds for boundary log kernels control residual-error
factors and establish screened comparison below the unit parameter.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- The explicit logarithmic kernel remains uniformly Lipschitz when extended
by zero below its ordered region. -/
theorem abs_upperRosserBoundaryLogKernel_sub_le_of_one_sixth_le
    {s a x y : ℝ} (ha : 1 / 6 ≤ a) :
    |LinearSieve.upperRosserBoundaryLogKernel s a x -
        LinearSieve.upperRosserBoundaryLogKernel s a y| ≤
      12 * |x - y| := by
  have hzero : ∀ {t : ℝ}, t ≤ a →
      LinearSieve.upperRosserBoundaryLogKernel s a t = 0 := by
    intro t ht
    rw [LinearSieve.upperRosserBoundaryLogKernel, if_neg]
    intro hactive
    exact (not_lt_of_ge ht) ((le_max_left _ _).trans_lt hactive)
  by_cases hx : a ≤ x
  · by_cases hy : a ≤ y
    · have h :=
        LinearSieve.abs_upperRosserBoundaryLogKernel_sub_le
          (s := s) (t := s) ha hx ha hy
      calc
        |LinearSieve.upperRosserBoundaryLogKernel s a x -
            LinearSieve.upperRosserBoundaryLogKernel s a y| ≤
            6 * (2 * |x - y| + |s - s| + 4 * |a - a|) := h
        _ = 12 * |x - y| := by simp; ring
    · have hy' : y ≤ a := (le_of_not_ge hy)
      have h :=
        LinearSieve.abs_upperRosserBoundaryLogKernel_sub_le
          (s := s) (t := s) ha hx ha (le_refl a)
      have hdist : |x - a| ≤ |x - y| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx),
          abs_of_nonneg (sub_nonneg.mpr (hy'.trans hx))]
        linarith
      rw [hzero hy']
      calc
        |LinearSieve.upperRosserBoundaryLogKernel s a x - 0| =
            |LinearSieve.upperRosserBoundaryLogKernel s a x -
              LinearSieve.upperRosserBoundaryLogKernel s a a| := by
                rw [hzero (le_refl a)]
        _ ≤ 6 * (2 * |x - a| + |s - s| + 4 * |a - a|) := h
        _ = 12 * |x - a| := by simp; ring
        _ ≤ 12 * |x - y| := mul_le_mul_of_nonneg_left hdist (by norm_num)
  · have hx' : x ≤ a := le_of_not_ge hx
    by_cases hy : a ≤ y
    · have h :=
        LinearSieve.abs_upperRosserBoundaryLogKernel_sub_le
          (s := s) (t := s) ha (le_refl a) ha hy
      have hdist : |a - y| ≤ |x - y| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hy),
          abs_of_nonpos (sub_nonpos.mpr (hx'.trans hy))]
        linarith
      rw [hzero hx']
      calc
        |0 - LinearSieve.upperRosserBoundaryLogKernel s a y| =
            |LinearSieve.upperRosserBoundaryLogKernel s a a -
              LinearSieve.upperRosserBoundaryLogKernel s a y| := by
                rw [hzero (le_refl a)]
        _ ≤ 6 * (2 * |a - y| + |s - s| + 4 * |a - a|) := h
        _ = 12 * |a - y| := by simp; ring
        _ ≤ 12 * |x - y| := mul_le_mul_of_nonneg_left hdist (by norm_num)
    · have hy' : y ≤ a := le_of_not_ge hy
      rw [hzero hx', hzero hy', sub_self, abs_zero]
      positivity

/-- The logarithm is Lipschitz above an arbitrary positive lower screen. -/
theorem abs_log_sub_log_le_inv_of_lower
    {c x y : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ c⁻¹ * |x - y| := by
  have hxpos : 0 < x := hc.trans_le hx
  have hypos : 0 < y := hc.trans_le hy
  have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hxpos hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hlog : Real.log y - Real.log x ≤ c⁻¹ * (y - x) := by
      rw [← Real.log_div hypos.ne' hxpos.ne']
      calc
        Real.log (y / x) ≤ y / x - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
        _ = x⁻¹ * (y - x) := by field_simp
        _ ≤ c⁻¹ * (y - x) :=
          mul_le_mul_of_nonneg_right ((inv_le_inv₀ hxpos hc).2 hx)
            (sub_nonneg.mpr hxy)
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hypos hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hlog : Real.log x - Real.log y ≤ c⁻¹ * (x - y) := by
      rw [← Real.log_div hxpos.ne' hypos.ne']
      calc
        Real.log (x / y) ≤ x / y - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
        _ = y⁻¹ * (x - y) := by field_simp
        _ ≤ c⁻¹ * (x - y) :=
          mul_le_mul_of_nonneg_right ((inv_le_inv₀ hypos hc).2 hy)
            (sub_nonneg.mpr hyx)
    linarith

/-- Logarithmic ratios are Lipschitz when all coordinates stay above a positive
screen. -/
theorem abs_log_div_sub_log_div_le_inv_of_lower
    {c x a y b : ℝ} (hc : 0 < c)
    (hx : c ≤ x) (ha : c ≤ a) (hy : c ≤ y) (hb : c ≤ b) :
    |Real.log (x / a) - Real.log (y / b)| ≤
      c⁻¹ * (|x - y| + |a - b|) := by
  have hx0 : x ≠ 0 := ne_of_gt (hc.trans_le hx)
  have ha0 : a ≠ 0 := ne_of_gt (hc.trans_le ha)
  have hy0 : y ≠ 0 := ne_of_gt (hc.trans_le hy)
  have hb0 : b ≠ 0 := ne_of_gt (hc.trans_le hb)
  rw [Real.log_div hx0 ha0, Real.log_div hy0 hb0]
  calc
    |(Real.log x - Real.log a) - (Real.log y - Real.log b)| =
        |(Real.log x - Real.log y) - (Real.log a - Real.log b)| := by ring_nf
    _ ≤ |Real.log x - Real.log y| + |Real.log a - Real.log b| := abs_sub _ _
    _ ≤ c⁻¹ * |x - y| + c⁻¹ * |a - b| :=
      add_le_add (abs_log_sub_log_le_inv_of_lower hc hx hy)
        (abs_log_sub_log_le_inv_of_lower hc ha hb)
    _ = c⁻¹ * (|x - y| + |a - b|) := by ring

/-- The logarithmic boundary kernel is uniformly Lipschitz on any fixed
positive screen. -/
theorem abs_upperRosserBoundaryLogKernel_sub_le_of_lower
    {c s a x₀ t b y₀ : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hax₀ : a ≤ x₀) (hb : c ≤ b) (hby₀ : b ≤ y₀) :
    |LinearSieve.upperRosserBoundaryLogKernel s a x₀ -
        LinearSieve.upperRosserBoundaryLogKernel t b y₀| ≤
      c⁻¹ * (2 * |x₀ - y₀| + |s - t| + 4 * |a - b|) := by
  have haPos : 0 < a := hc.trans_le ha
  have hbPos : 0 < b := hc.trans_le hb
  rw [LinearSieve.upperRosserBoundaryLogKernel_eq_max_log_sub haPos hax₀,
    LinearSieve.upperRosserBoundaryLogKernel_eq_max_log_sub hbPos hby₀]
  let d := max a (s - x₀ - 3 * a)
  let e := max b (t - y₀ - 3 * b)
  have hd : c ≤ d := ha.trans (le_max_left _ _)
  have he : c ≤ e := hb.trans (le_max_left _ _)
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
        c⁻¹ * (|x₀ - y₀| + |d - e|) := by
    calc
      |(Real.log x₀ - Real.log d) - (Real.log y₀ - Real.log e)| =
          |Real.log (x₀ / d) - Real.log (y₀ / e)| := by
            rw [Real.log_div (ne_of_gt (haPos.trans_le hax₀))
              (ne_of_gt (hc.trans_le hd)),
              Real.log_div (ne_of_gt (hbPos.trans_le hby₀))
                (ne_of_gt (hc.trans_le he))]
      _ ≤ c⁻¹ * (|x₀ - y₀| + |d - e|) :=
        abs_log_div_sub_log_div_le_inv_of_lower hc
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
  exact hmax.trans <| hlogs.trans <|
    mul_le_mul_of_nonneg_left (by linarith [hden]) (inv_nonneg.mpr hc.le)

/-- The logarithmic boundary kernel is bounded on an arbitrary positive
screen. -/
theorem upperRosserBoundaryLogKernel_le_log_inv_of_lower
    {c s a x₀ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : c ≤ a) (hx₀ : x₀ ≤ 1) :
    LinearSieve.upperRosserBoundaryLogKernel s a x₀ ≤ Real.log c⁻¹ := by
  rw [LinearSieve.upperRosserBoundaryLogKernel]
  split_ifs with hcell
  · have hden : 0 < max a (s - x₀ - 3 * a) :=
      hc.trans_le (ha.trans (le_max_left _ _))
    apply Real.log_le_log (div_pos (hden.trans hcell) hden)
    apply (div_le_iff₀ hden).2
    have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    have hone : 1 ≤ c⁻¹ * max a (s - x₀ - 3 * a) := by
      calc
        1 = c⁻¹ * c := by field_simp
        _ ≤ c⁻¹ * max a (s - x₀ - 3 * a) :=
          mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) hcinv
    exact hx₀.trans hone
  · exact Real.log_nonneg ((one_le_inv₀ hc).2 hc1)

/-- Extending the logarithmic boundary kernel by zero below its ordered region
preserves a Lipschitz bound on an arbitrary positive screen. -/
theorem abs_upperRosserBoundaryLogKernel_sub_le_of_screen
    {c s a x y : ℝ} (hc : 0 < c) (ha : c ≤ a) :
    |LinearSieve.upperRosserBoundaryLogKernel s a x -
        LinearSieve.upperRosserBoundaryLogKernel s a y| ≤
      (2 * c⁻¹) * |x - y| := by
  have hzero : ∀ {t : ℝ}, t ≤ a →
      LinearSieve.upperRosserBoundaryLogKernel s a t = 0 := by
    intro t ht
    rw [LinearSieve.upperRosserBoundaryLogKernel, if_neg]
    intro hactive
    exact (not_lt_of_ge ht) ((le_max_left _ _).trans_lt hactive)
  by_cases hx : a ≤ x
  · by_cases hy : a ≤ y
    · have h :=
        abs_upperRosserBoundaryLogKernel_sub_le_of_lower
          (s := s) (t := s) hc ha hx ha hy
      calc
        _ ≤ c⁻¹ * (2 * |x - y| + |s - s| + 4 * |a - a|) := h
        _ = (2 * c⁻¹) * |x - y| := by simp; ring
    · have hy' : y ≤ a := le_of_not_ge hy
      have h :=
        abs_upperRosserBoundaryLogKernel_sub_le_of_lower
          (s := s) (t := s) hc ha hx ha (le_refl a)
      have hdist : |x - a| ≤ |x - y| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx),
          abs_of_nonneg (sub_nonneg.mpr (hy'.trans hx))]
        linarith
      rw [hzero hy']
      calc
        |LinearSieve.upperRosserBoundaryLogKernel s a x - 0| =
            |LinearSieve.upperRosserBoundaryLogKernel s a x -
              LinearSieve.upperRosserBoundaryLogKernel s a a| := by
                rw [hzero (le_refl a)]
        _ ≤ c⁻¹ * (2 * |x - a| + |s - s| + 4 * |a - a|) := h
        _ = (2 * c⁻¹) * |x - a| := by simp; ring
        _ ≤ (2 * c⁻¹) * |x - y| :=
          mul_le_mul_of_nonneg_left hdist (by positivity)
  · have hx' : x ≤ a := le_of_not_ge hx
    by_cases hy : a ≤ y
    · have h :=
        abs_upperRosserBoundaryLogKernel_sub_le_of_lower
          (s := s) (t := s) hc ha (le_refl a) ha hy
      have hdist : |a - y| ≤ |x - y| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hy),
          abs_of_nonpos (sub_nonpos.mpr (hx'.trans hy))]
        linarith
      rw [hzero hx']
      calc
        |0 - LinearSieve.upperRosserBoundaryLogKernel s a y| =
            |LinearSieve.upperRosserBoundaryLogKernel s a a -
              LinearSieve.upperRosserBoundaryLogKernel s a y| := by
                rw [hzero (le_refl a)]
        _ ≤ c⁻¹ * (2 * |a - y| + |s - s| + 4 * |a - a|) := h
        _ = (2 * c⁻¹) * |a - y| := by simp; ring
        _ ≤ (2 * c⁻¹) * |x - y| :=
          mul_le_mul_of_nonneg_left hdist (by positivity)
    · have hy' : y ≤ a := le_of_not_ge hy
      rw [hzero hx', hzero hy', sub_self, abs_zero]
      positivity

/-- Uniform two-stage Stieltjes transfer for the first positive residual depth.
The distinguished prime is screened away from zero, while the exact inherited
upper face `b` is retained. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_one_le_boundaryMassAux_add_screened
    (K ρ c : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hc : 0 < c)
    (hc1 : c < 1) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s b : ℝ) (q : ℕ) (P : Finset ℕ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) →
        (∀ p ∈ P, Real.log p / Real.log z < b) →
        c ≤ Real.log q / Real.log z → b ≤ 1 →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P 1 ≤
          LinearSieve.upperRosserBoundaryMassAux 1 s
            (Real.log q / Real.log z) b + ρ := by
  let ε₁ : ℝ := ρ / (4 * (c⁻¹ + 1))
  let ε₀ : ℝ := ρ / 2
  let B : ℝ := Real.log c⁻¹ + ε₁
  have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (Real.log_nonneg ((one_le_inv₀ hc).2 hc1.le)) hε₁.le
  obtain ⟨zInner, hzInner, hinner⟩ :=
    exists_sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_logKernel_add_screened
      K ε₁ c hK hε₁ hc hc1
  obtain ⟨zOuter, hzOuter, houter⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_Ioo_add_screened
      K ε₀ B (2 * c⁻¹) c hK hε₀ hB (by positivity) hc hc1
  let z₀ := max zInner zOuter
  refine ⟨z₀, hzInner.trans (le_max_left _ _), ?_⟩
  intro S z Δ s b q P hz hΔ hlocal hs hqprime hqs hP hqmin hupper hqa hb
  have hzInnerZ : zInner ≤ z := (le_max_left _ _).trans hz
  have hzOuterZ : zOuter ≤ z := (le_max_right _ _).trans hz
  have hz2 : 2 ≤ z := hzInner.trans hzInnerZ
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) hz2
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  let a : ℝ := Real.log q / Real.log z
  let r : ℝ := min b (s / 3)
  let P₀ : Finset ℕ :=
    P.filter (fun p₀ : ℕ => Real.log p₀ / Real.log z ≤ r)
  let inner : ℕ → ℝ := fun p₀ =>
    ∑ p₁ ∈ P.filter
        (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
      (S.nu p₁ / (1 - S.nu p₁)) *
        LinearSieve.upperRosserBoundaryMassAux 0
          (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
          a (Real.log p₁ / Real.log z)
  have ha : c ≤ a := by simpa [a] using hqa
  have haPos : 0 < a := hc.trans_le ha
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (min_le_left b (s / 3)).trans hb
  have hpointwise :
      LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          (fun p => S.nu p / (1 - S.nu p))
          (Nat.floor Δ + 1) q P 1 ≤
        ∑ p₀ ∈ P₀, (S.nu p₀ / (1 - S.nu p₀)) * inner p₀ := by
    have h :=
      upperRosserBoundaryChainsFixedDepthDensity_one_le_screenedResidualBoundaryMassAux
        (fun p => S.nu p / (1 - S.nu p)) hz1 hΔ hs hqs hqprime
        (fun p hp => Nat.prime_of_mem_primeFactors (hP hp)) hqmin hupper
        (fun p hp => nu_div_one_sub_nonneg_of_mem (hP hp))
    simpa only [P₀, inner, a, r, Finset.filter_filter, and_assoc,
      Finset.mul_sum, mul_assoc] using h
  by_cases hP₀ne : P₀.Nonempty
  · have hP₀ : P₀ ⊆ S.prodPrimes.primeFactors := by
      intro p hp
      exact hP (Finset.mem_filter.mp hp).1
    have hP₀coord : ∀ p₀ ∈ P₀,
        Real.log p₀ / Real.log z ∈ Set.Icc a r := by
      intro p₀ hp₀
      have hp₀' := Finset.mem_filter.mp hp₀
      have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀'.1)
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
      have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
      have hqp₀ : q < p₀ := lt_of_le_of_ne (hqmin p₀ hp₀'.1) (by
        intro hEq
        apply hqs
        simpa [hEq] using hp₀'.1)
      exact ⟨by
        dsimp [a]
        exact (div_lt_div_iff_of_pos_right hlogz).2
          ((Real.strictMonoOn_log.lt_iff_lt hqpos hp₀pos).2
            (by exact_mod_cast hqp₀)) |>.le,
        hp₀'.2⟩
    have har : a ≤ r := by
      obtain ⟨p₀, hp₀⟩ := hP₀ne
      exact (hP₀coord p₀ hp₀).1.trans (hP₀coord p₀ hp₀).2
    have hInnerBound : ∀ p₀ ∈ P₀,
        inner p₀ ≤
          LinearSieve.upperRosserBoundaryLogKernel s a
            (Real.log p₀ / Real.log z) + ε₁ := by
      intro p₀ hp₀
      have hp₀P := (Finset.mem_filter.mp hp₀).1
      have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀P)
      have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
      apply hinner S z s (Real.log p₀ / Real.log z) a
        (P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1))
        hzInnerZ hlocal ha ((hP₀coord p₀ hp₀).2.trans hr1)
      · intro p hp
        exact hP (Finset.mem_filter.mp hp).1
      · intro p₁ hp₁
        have hp₁' := Finset.mem_filter.mp hp₁
        have hp₁prime : p₁.Prime := Nat.prime_of_mem_primeFactors (hP hp₁'.1)
        have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
        have hqp₁ : q < p₁ := lt_of_le_of_ne (hqmin p₁ hp₁'.1) (by
          intro hEq
          apply hqs
          simpa [hEq] using hp₁'.1)
        constructor
        · dsimp [a]
          exact (div_lt_div_iff_of_pos_right hlogz).2
            ((Real.strictMonoOn_log.lt_iff_lt hqpos hp₁pos).2
              (by exact_mod_cast hqp₁))
        · exact (div_lt_div_iff_of_pos_right hlogz).2
            ((Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
              (by exact_mod_cast hp₁'.2.1))
    have hInnerNonneg : ∀ p₀ ∈ P₀, 0 ≤ inner p₀ := by
      intro p₀ hp₀
      apply Finset.sum_nonneg
      intro p₁ hp₁
      exact mul_nonneg
        (nu_div_one_sub_nonneg_of_mem
          (hP (Finset.mem_filter.mp hp₁).1))
        (LinearSieve.upperRosserBoundaryMassAux_nonneg 0 haPos.le)
    let f : ℝ → ℝ := fun x =>
      LinearSieve.upperRosserBoundaryLogKernel s a x + ε₁
    have hfNonneg : ∀ x ∈ Set.Icc (c : ℝ) 1, 0 ≤ f x := by
      intro x hx
      exact add_nonneg
        (LinearSieve.upperRosserBoundaryLogKernel_nonneg haPos) hε₁.le
    have hfB : ∀ x ∈ Set.Icc (c : ℝ) 1, f x ≤ B := by
      intro x hx
      dsimp [f, B]
      linarith [upperRosserBoundaryLogKernel_le_log_inv_of_lower
        (s := s) hc hc1.le ha hx.2]
    have hfLip : ∀ x ∈ Set.Icc (c : ℝ) 1,
        ∀ y ∈ Set.Icc (c : ℝ) 1,
          |f x - f y| ≤ (2 * c⁻¹) * |x - y| := by
      intro x hx y hy
      simpa only [f, add_sub_add_right_eq_sub] using
        abs_upperRosserBoundaryLogKernel_sub_le_of_screen hc ha
          (x := x) (y := y) (s := s)
    have hinv :
        MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹)
          (Set.Ioo c 1) := by
      apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hc1.le).1
      apply intervalIntegral.intervalIntegrable_inv (f := fun x : ℝ => x)
      · intro x hx
        rw [Set.uIcc_of_le hc1.le] at hx
        exact ne_of_gt (hc.trans_le hx.1)
      · exact continuous_id.continuousOn
    have hfInt : MeasureTheory.IntegrableOn
        (fun x => x⁻¹ * f x) (Set.Ioo c 1) := by
      have hfinite :
          MeasureTheory.volume (Set.Ioo c 1) < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top
      apply MeasureTheory.IntegrableOn.of_bound hfinite
        (measurable_id.inv.mul
          ((LinearSieve.measurable_upperRosserBoundaryLogKernel s a).add
            measurable_const)).aestronglyMeasurable
        (c⁻¹ * B)
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      have hxpos : 0 < x := hc.trans hx.1
      have hxinv : x⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hxpos hc).2 hx.1.le
      change |x⁻¹ * f x| ≤ c⁻¹ * B
      rw [abs_of_nonneg
        (mul_nonneg (inv_nonneg.mpr hxpos.le)
          (hfNonneg x ⟨hx.1.le, hx.2.le⟩))]
      exact mul_le_mul hxinv (hfB x ⟨hx.1.le, hx.2.le⟩)
        (hfNonneg x ⟨hx.1.le, hx.2.le⟩) (inv_nonneg.mpr hc.le)
    have houterBound :=
      houter S z P₀ inner f a r hzOuterZ hlocal hP₀ ha har hr1 hP₀coord
        hfNonneg hfB hfLip hfInt (by
          intro p₀ hp₀
          exact ⟨hInnerNonneg p₀ hp₀, hInnerBound p₀ hp₀⟩)
    have hintervalSubset :
        Set.Ioo a r ⊆ Set.Ioo c 1 := by
      intro x hx
      exact ⟨ha.trans_lt hx.1, hx.2.trans_le hr1⟩
    have hkInt :
        MeasureTheory.IntegrableOn
          (fun x => x⁻¹ *
            LinearSieve.upperRosserBoundaryLogKernel s a x)
          (Set.Ioo a r) := by
      have hfinite : MeasureTheory.volume (Set.Ioo a r) < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top
      apply MeasureTheory.IntegrableOn.of_bound hfinite
        (measurable_id.inv.mul
          (LinearSieve.measurable_upperRosserBoundaryLogKernel s a)
            ).aestronglyMeasurable
        (c⁻¹ * Real.log c⁻¹)
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      have hxpos : 0 < x := haPos.trans hx.1
      have hxinv : x⁻¹ ≤ c⁻¹ :=
        (inv_le_inv₀ hxpos hc).2 (ha.trans hx.1.le)
      have hkNonneg :=
        LinearSieve.upperRosserBoundaryLogKernel_nonneg (s := s) (x₀ := x) haPos
      have hkBound :=
        upperRosserBoundaryLogKernel_le_log_inv_of_lower
          (s := s) (x₀ := x) hc hc1.le ha (hx.2.le.trans hr1)
      change |x⁻¹ * LinearSieve.upperRosserBoundaryLogKernel s a x| ≤
        c⁻¹ * Real.log c⁻¹
      rw [abs_of_nonneg
        (mul_nonneg (inv_nonneg.mpr hxpos.le) hkNonneg)]
      exact mul_le_mul hxinv hkBound hkNonneg (inv_nonneg.mpr hc.le)
    have heInt :
        MeasureTheory.IntegrableOn (fun x => x⁻¹ * ε₁) (Set.Ioo a r) :=
      (hinv.mono_set hintervalSubset).mul_const ε₁
    have heIntegral : (∫ x in Set.Ioo a r, x⁻¹ * ε₁) ≤ c⁻¹ * ε₁ := by
      have hfinite : MeasureTheory.volume (Set.Ioo a r) ≠ ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top
      have hconst :
          MeasureTheory.IntegrableOn (fun _ : ℝ => c⁻¹ * ε₁) (Set.Ioo a r) :=
        MeasureTheory.integrableOn_const hfinite
      calc
        (∫ x in Set.Ioo a r, x⁻¹ * ε₁) ≤
            ∫ _x in Set.Ioo a r, c⁻¹ * ε₁ := by
          apply MeasureTheory.setIntegral_mono_on heInt hconst measurableSet_Ioo
          intro x hx
          have hxpos : 0 < x := haPos.trans hx.1
          have hxinv : x⁻¹ ≤ c⁻¹ :=
            (inv_le_inv₀ hxpos hc).2 (ha.trans hx.1.le)
          exact mul_le_mul_of_nonneg_right hxinv hε₁.le
        _ = (r - a) * (c⁻¹ * ε₁) := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
            Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr har)]
          rfl
        _ ≤ c⁻¹ * ε₁ := by
          have hlength : r - a ≤ 1 := by linarith [hr1, haPos.le]
          exact mul_le_of_le_one_left (mul_nonneg (inv_nonneg.mpr hc.le) hε₁.le)
            hlength
    have hintegral :
        (∫ x in Set.Ioo a r, x⁻¹ * f x) ≤
          LinearSieve.upperRosserBoundaryMassAux 1 s a b + c⁻¹ * ε₁ := by
      rw [show (fun x => x⁻¹ * f x) = (fun x =>
          x⁻¹ * LinearSieve.upperRosserBoundaryLogKernel s a x + x⁻¹ * ε₁) by
            funext x
            simp only [f]
            ring,
        MeasureTheory.integral_add hkInt heInt,
        ← LinearSieve.upperRosserBoundaryMassAux_one_eq_integral_logKernel haPos]
      linarith
    have hsum :
        (∑ p₀ ∈ P₀, (S.nu p₀ / (1 - S.nu p₀)) * inner p₀) =
          ∑ p₀ ∈ P₀, inner p₀ * (S.nu p₀ / (1 - S.nu p₀)) := by
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      ring
    calc
      LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P 1 ≤
          ∑ p₀ ∈ P₀, (S.nu p₀ / (1 - S.nu p₀)) * inner p₀ := hpointwise
      _ = ∑ p₀ ∈ P₀, inner p₀ * (S.nu p₀ / (1 - S.nu p₀)) := hsum
      _ ≤ (∫ x in Set.Ioo a r, x⁻¹ * f x) + ε₀ := houterBound
      _ ≤ LinearSieve.upperRosserBoundaryMassAux 1 s a b +
            c⁻¹ * ε₁ + ε₀ := by linarith
      _ ≤ LinearSieve.upperRosserBoundaryMassAux 1 s
            (Real.log q / Real.log z) b + ρ := by
        have hratio : c⁻¹ / (c⁻¹ + 1) ≤ 1 := by
          apply (div_le_iff₀ (by positivity : 0 < c⁻¹ + 1)).2
          linarith
        have hterm : c⁻¹ * ε₁ ≤ ρ / 4 := by
          calc
            c⁻¹ * ε₁ = (ρ / 4) * (c⁻¹ / (c⁻¹ + 1)) := by
              dsimp [ε₁]
              field_simp
            _ ≤ (ρ / 4) * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = ρ / 4 := by ring
        dsimp [a, ε₀]
        nlinarith
  · have hP₀empty : P₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP₀ne
    calc
      LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P 1 ≤
          ∑ p₀ ∈ P₀, (S.nu p₀ / (1 - S.nu p₀)) * inner p₀ := hpointwise
      _ = 0 := by rw [hP₀empty]; simp
      _ ≤ LinearSieve.upperRosserBoundaryMassAux 1 s
            (Real.log q / Real.log z) b + ρ :=
        add_nonneg
          (LinearSieve.upperRosserBoundaryMassAux_nonneg 1 haPos.le) hρ.le

/-- Compatibility specialization of the depth-one comparison to the
traditional one-sixth screen. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_one_le_boundaryMassAux_add
    (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s b : ℝ) (q : ℕ) (P : Finset ℕ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) →
        (∀ p ∈ P, Real.log p / Real.log z < b) →
        1 / 6 ≤ Real.log q / Real.log z → b ≤ 1 →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P 1 ≤
          LinearSieve.upperRosserBoundaryMassAux 1 s
            (Real.log q / Real.log z) b + ρ :=
  exists_upperRosserBoundaryChainsFixedDepthDensity_one_le_boundaryMassAux_add_screened
    K ρ (1 / 6) hK hρ (by norm_num) (by norm_num)

/-- Above a fixed cutoff depending only on the local-product constant and a
positive screen, the residual-error factor is uniformly bounded. -/
theorem exists_upperRosserResidualErrorFactor_le
    (K c : ℝ) (hK : 1 ≤ K) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
      -1 ≤ Real.log (z + 1) / Real.log (z ^ c) *
         (1 + K / Real.log (z ^ c)) - 1 ∧
      Real.log (z + 1) / Real.log (z ^ c) *
         (1 + K / Real.log (z ^ c)) - 1 ≤ 4 / c := by
  let z₀ := max 2 (Real.exp (K / c))
  refine ⟨z₀, ?_, ?_⟩
  · exact le_max_left _ _
  intro z hz
  have hz2 : (2 : ℝ) ≤ z := (le_max_left _ _).trans hz
  have hzexp : Real.exp (K / c) ≤ z := (le_max_right _ _).trans hz
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogpow :
      Real.log (z ^ c) = c * Real.log z := by
    rw [Real.log_rpow hzpos]
  have hden : 0 < Real.log (z ^ c) := by
    rw [hlogpow]
    positivity
  have hlogK : K / c ≤ Real.log z := by
    calc
      K / c = Real.log (Real.exp (K / c)) := (Real.log_exp _).symm
      _ ≤ Real.log z := Real.strictMonoOn_log.monotoneOn (Real.exp_pos _)
       ((Real.exp_pos _).trans_le hzexp) hzexp
  have herror : K / Real.log (z ^ c) ≤ 1 := by
    rw [hlogpow]
    apply (div_le_iff₀ (mul_pos hc hlogz)).2
    have := (div_le_iff₀ hc).1 hlogK
    nlinarith
  have hlogSq : Real.log (z + 1) ≤ 2 * Real.log z := by
    have hsq : z + 1 ≤ z ^ 2 := by nlinarith
    calc
      Real.log (z + 1) ≤ Real.log (z ^ 2) := by
       apply Real.strictMonoOn_log.monotoneOn
       · exact Set.mem_Ioi.mpr (by linarith)
       · exact Set.mem_Ioi.mpr (pow_pos hzpos 2)
       · exact hsq
      _ = 2 * Real.log z := by rw [Real.log_pow]; norm_num
  have hratio :
      Real.log (z + 1) / Real.log (z ^ c) ≤ 2 / c := by
    rw [hlogpow]
    apply (div_le_iff₀ (mul_pos hc hlogz)).2
    calc
      Real.log (z + 1) ≤ 2 * Real.log z := hlogSq
      _ = 2 / c * (c * Real.log z) := by field_simp
  have hratioNonneg :
      0 ≤ Real.log (z + 1) / Real.log (z ^ c) :=
    div_nonneg (Real.log_nonneg (by linarith)) hden.le
  have herrorNonneg : 0 ≤ K / Real.log (z ^ c) :=
    div_nonneg (by linarith) hden.le
  constructor
  · nlinarith [mul_nonneg hratioNonneg
      (by linarith : 0 ≤ 1 + K / Real.log (z ^ c))]
  · have hproduct := mul_le_mul hratio
       (show 1 + K / Real.log (z ^ c) ≤ 2 by linarith)
       (show 0 ≤ 1 + K / Real.log (z ^ c) by linarith)
       (by positivity : (0 : ℝ) ≤ 2 / c)
    calc
      Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1 ≤
          (2 / c) * 2 - 1 := by linarith
      _ ≤ (2 / c) * 2 := by linarith
      _ = 4 / c := by ring

/-- A screened positive-depth residual comparison advances by one Rosser pair.
The inherited upper face is retained, and every analytic cutoff is uniform on
the displayed compact level interval. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_succ_le_boundaryMassAux_add
    (k : ℕ) (K ρ c s₀ s₁ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hc : 0 < c) (hc1 : c < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s b : ℝ) (q : ℕ) (P : Finset ℕ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z → s ∈ Set.Icc s₀ s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) →
        (∀ p ∈ P, Real.log p / Real.log z < b) →
        c ≤ Real.log q / Real.log z → b ≤ 1 →
        UpperRosserBoundaryScreenedResidualComparison S z q (k + 1) ε c s₁ →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 2) ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 2) s
            (Real.log q / Real.log z) b + ρ := by
  let A : ℝ := (c⁻¹ * c⁻¹) ^ (k + 1)
  let A₂ : ℝ := (c⁻¹ * c⁻¹) ^ (k + 2)
  let CInner : ℝ := 2 + 2 / c + A / c ^ 2 + c⁻¹ * A
  let COuter : ℝ := A₂ + 1 / c + c⁻¹ * A / c ^ 2 + 1
  let C : ℝ := COuter + (c⁻¹ + 1) * CInner +
    (1 + 4 / c + (4 / c) ^ 2)
  let ε : ℝ := min 1 (ρ / (C + 1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hCInner : 0 ≤ CInner := by dsimp [CInner]; positivity
  have hCOuter : 0 ≤ COuter := by dsimp [COuter]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hρ (by positivity))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεratio : ε ≤ ρ / (C + 1) := min_le_right _ _
  have hεC : ε * C ≤ ρ := by
    have hmul := mul_le_mul_of_nonneg_right hεratio hC
    have hfrac : ρ / (C + 1) * C ≤ ρ := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < C + 1)).2
      nlinarith
    exact hmul.trans hfrac
  obtain ⟨NCorner, hCorner⟩ :=
    exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform_cutoffs
      k (s₀ := s₀) (s₁ := s₁) (c := c) (ε := ε) hc hc1 hε
  obtain ⟨NInner, hInner⟩ :=
    exists_upperRosserFixedDepthMesh_correctedInnerDarboux_succ_le_trueIntegral_add
      k (K := K) (s₀ := s₀) (s₁ := s₁) (c := c)
        (ε := ε) (η := ε) (ρ := ε) (B := A + ε)
        (by linarith) hc hc1 hε.le hε hε
        (add_nonneg hA hε.le)
  obtain ⟨NOuter, hOuter⟩ :=
    exists_upperRosserFixedDepthMesh_correctedScreenedOuterDarboux_succ_movingLower_le_massAux_add
      k (K := K) (s₀ := s₀) (s₁ := s₁) (c := c)
        (ε := ε) (ρ := ε) (by linarith) hc hc1 hε hε
  obtain ⟨NWidth, hNWidth⟩ :
      ∃ NWidth : ℕ, (1 - c) / ε < NWidth := exists_nat_gt _
  let m := max NCorner (max NInner (max NOuter NWidth))
  have hmCorner : NCorner ≤ m := le_max_left _ _
  have hmInner : NInner ≤ m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hmOuter : NOuter ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmWidth : NWidth ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hwidth :
      upperRosserFixedDepthMeshWidth c m < ε := by
    have hmReal : (1 - c) / ε < (m : ℝ) :=
      hNWidth.trans_le (by exact_mod_cast hmWidth)
    have hcross : 1 - c < ε * (m : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hε).1 hmReal
    dsimp [upperRosserFixedDepthMeshWidth]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  obtain ⟨zInner, hzInner, hInnerZ⟩ := hInner m hmInner
  obtain ⟨zOuter, hzOuter, hOuterZ⟩ := hOuter m hmOuter
  obtain ⟨zTwo, hzTwo, hTwo⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_twoPartitions_add_screened
      (k + 1) (Fin (m + 1)) (Fin (m + 1)) K ε A (c⁻¹ * A + CInner)
        c hK hε hA
        (add_nonneg (mul_nonneg (inv_nonneg.mpr hc.le) hA) hCInner) hc
  obtain ⟨zInc, hzInc, hInc⟩ :=
    exists_upperRosserFixedDepthMesh_correctedIncrementSum_le
      m (K := K) (ρ := ε) (c := c)
        (by linarith) hε hc hc1
  obtain ⟨zFactor, hzFactor, hFactor⟩ :=
    exists_upperRosserResidualErrorFactor_le K c hK hc
  let zPow : ℝ := (2 : ℝ) ^ (1 / c)
  let z₀ := max 2
    (max zPow (max zInner (max zOuter (max zTwo (max zInc zFactor)))))
  refine ⟨ε, hε, z₀, ?_, ?_⟩
  · exact le_max_left _ _
  intro S z Δ s b q P hz hΔ hlocal hs hsRange hqprime hqs hP hqmin hupper hqa hb
    hcomparison
  have hzRest :
      max zPow (max zInner (max zOuter (max zTwo (max zInc zFactor)))) ≤ z :=
    (le_max_right _ _).trans hz
  have hzPow : zPow ≤ z := (le_max_left _ _).trans hzRest
  have hzCutoffs : max zInner (max zOuter (max zTwo (max zInc zFactor))) ≤ z :=
    (le_max_right _ _).trans hzRest
  have hzInnerZ : zInner ≤ z :=
    (le_max_left _ _).trans hzCutoffs
  have hzOuterZ : zOuter ≤ z :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans hzCutoffs)
  have hzTwoZ : zTwo ≤ z :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans hzCutoffs))
  have hzIncZ : zInc ≤ z :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans hzCutoffs)))
  have hzFactorZ : zFactor ≤ z :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans hzCutoffs)))
  have hz2 : (2 : ℝ) ≤ z := (le_max_left _ _).trans hz
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hzc : 2 ≤ z ^ c := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
      _ = ((2 : ℝ) ^ (1 / c)) ^ c := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        field_simp
      _ ≤ z ^ c :=
        Real.rpow_le_rpow (by positivity) hzPow hc.le
  let a : ℝ := Real.log q / Real.log z
  let r : ℝ := min b (s / 3)
  have ha : c ≤ a := by simpa [a] using hqa
  have haPos : 0 < a := hc.trans_le ha
  have hcut : ∀ p ∈ P, (p : ℝ) ≤ z := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hcoord : Real.log p / Real.log z < 1 := (hupper p hp).trans_le hb
    have hlog : Real.log p < Real.log z := by
      apply (div_lt_one hlogz).mp
      simpa using hcoord
    exact (Real.strictMonoOn_log.lt_iff_lt hppos hzpos).mp hlog |>.le
  have hscreen : ∀ p ∈ P, c ≤ Real.log p / Real.log z := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hlog : Real.log q ≤ Real.log p :=
      Real.strictMonoOn_log.monotoneOn hqpos hppos (by exact_mod_cast hqmin p hp)
    exact ha.trans ((div_le_div_iff_of_pos_right hlogz).2 hlog)
  by_cases har : a ≤ r
  · have ha1 : a ≤ 1 := har.trans (min_le_left b (s / 3) |>.trans hb)
    let cell : ℕ → Fin (m + 1) :=
      fun p => upperRosserFixedDepthMeshCell c m
        (Real.log p / Real.log z)
    let h : Fin (m + 1) := cell q
    let w : ℝ := upperRosserFixedDepthMeshWidth c m
    let E : ℝ := ε + (ε + ε) / c +
      A * w / c ^ 2 + c⁻¹ * A * w + ε
    let innerMajorant : ℕ → Fin (m + 1) → ℝ := fun p₀ i =>
      if upperRosserFixedDepthMeshRight c m (cell p₀) ≤ r + w ∧
          upperRosserFixedDepthMeshLeft c m i <
            upperRosserFixedDepthMeshRight c m (cell p₀) then
        LinearSieve.upperRosserBoundaryMassAux (k + 1)
          (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
            upperRosserFixedDepthMeshRight c m i)
          (upperRosserFixedDepthMeshLeft c m h)
          (upperRosserFixedDepthMeshRight c m i) + ε
      else 0
    let outerMajorant : Fin (m + 1) → ℝ := fun j =>
      if upperRosserFixedDepthMeshRight c m j ≤ r + w then
        (∫ x in Set.Ioo a (upperRosserFixedDepthMeshRight c m j),
          x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - upperRosserFixedDepthMeshRight c m j - x) a x) + E
      else 0
    have hcell : ∀ p ∈ P,
        Real.log p / Real.log z ∈ Set.Icc
          (upperRosserFixedDepthMeshLeft c m (cell p))
          (upperRosserFixedDepthMeshRight c m (cell p)) := by
      intro p hp
      exact upperRosserFixedDepthMeshCell_bounds hc1 m
        ⟨hscreen p hp, (hupper p hp).le.trans hb⟩
    have hqcell : a ∈ Set.Icc
        (upperRosserFixedDepthMeshLeft c m h)
        (upperRosserFixedDepthMeshRight c m h) := by
      dsimp [h, cell]
      exact upperRosserFixedDepthMeshCell_bounds hc1 m ⟨ha, ha1⟩
    have hincNonneg : ∀ i : Fin (m + 1), 0 ≤
        upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i *
          (1 + K / (upperRosserFixedDepthMeshLeft c m i *
            Real.log z)) - 1 := by
      intro i
      have hleft : 0 < upperRosserFixedDepthMeshLeft c m i :=
        hc.trans_le (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
      have hratio : 1 ≤
          upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i :=
        (le_div_iff₀ hleft).2
          (by simpa using (upperRosserFixedDepthMeshLeft_le_right
            (c := c) hc1 m i))
      have hcorr : 1 ≤ 1 + K /
          (upperRosserFixedDepthMeshLeft c m i * Real.log z) := by
        apply le_add_of_nonneg_right
        exact div_nonneg (by linarith)
          (mul_pos hleft hlogz).le
      nlinarith [mul_le_mul hratio hcorr zero_le_one
        (zero_le_one.trans hratio)]
    have hE : 0 ≤ E := by
      dsimp [E]
      exact add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg hε.le
            (div_nonneg (add_nonneg hε.le hε.le) hc.le))
            (div_nonneg
              (mul_nonneg hA
                (upperRosserFixedDepthMeshWidth_pos (c := c)
                hc1 m).le)
              (sq_nonneg c)))
          (mul_nonneg
          (mul_nonneg (inv_nonneg.mpr hc.le) hA)
            (upperRosserFixedDepthMeshWidth_pos (c := c)
            hc1 m).le))
        hε.le
    have hEbound : E ≤ ε * CInner := by
      have hwle : w ≤ ε := hwidth.le
      have hAw : A * w ≤ A * ε :=
        mul_le_mul_of_nonneg_left hwle hA
      dsimp [E, CInner]
      have hcne : c ≠ 0 := ne_of_gt hc
      have hcSq : 0 < c ^ 2 := sq_pos_of_pos hc
      have hAwDiv : A * w / c ^ 2 ≤ A * ε / c ^ 2 :=
        div_le_div_of_nonneg_right hAw hcSq.le
      have hcInvAw : c⁻¹ * A * w ≤ c⁻¹ * A * ε :=
        calc
          c⁻¹ * A * w = c⁻¹ * (A * w) := by ring
          _ ≤ c⁻¹ * (A * ε) :=
            mul_le_mul_of_nonneg_left hAw (inv_nonneg.mpr hc.le)
          _ = c⁻¹ * A * ε := by ring
      have htwoDiv : (ε + ε) / c = ε * (2 / c) := by
        field_simp
        ring
      rw [htwoDiv]
      calc
        ε + ε * (2 / c) + A * w / c ^ 2 + c⁻¹ * A * w + ε ≤
            ε + ε * (2 / c) + A * ε / c ^ 2 + c⁻¹ * A * ε + ε := by
          linarith
        _ = ε * (2 + 2 / c + A / c ^ 2 + c⁻¹ * A) := by ring
    have hinnerMajorantNonneg : ∀ p₀, ∀ i, 0 ≤ innerMajorant p₀ i := by
      intro p₀ i
      dsimp [innerMajorant]
      split_ifs
      · exact add_nonneg
          (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1)
            (hc.le.trans (upperRosserFixedDepthMeshLeft_mem hc1 m h).1))
          hε.le
      · exact le_rfl
    have houterMajorantNonneg : ∀ j, 0 ≤ outerMajorant j := by
      intro j
      dsimp [outerMajorant]
      split_ifs
      · exact add_nonneg (MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          exact mul_nonneg (inv_nonneg.mpr (haPos.le.trans hx.1.le))
            (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1) haPos.le))) hE
      · exact le_rfl
    have hinnerCornerBound : ∀ j i : Fin (m + 1),
        LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - upperRosserFixedDepthMeshRight c m j -
              upperRosserFixedDepthMeshRight c m i)
            (upperRosserFixedDepthMeshLeft c m h)
            (upperRosserFixedDepthMeshRight c m i) + ε ≤ A + ε := by
      intro j i
      have hmass :
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - upperRosserFixedDepthMeshRight c m j -
                upperRosserFixedDepthMeshRight c m i)
              (upperRosserFixedDepthMeshLeft c m h)
              (upperRosserFixedDepthMeshRight c m i) ≤ A := by
        simpa [A] using
          LinearSieve.upperRosserBoundaryMassAux_le_of_lower_bound
            (k + 1)
            (s := s - upperRosserFixedDepthMeshRight c m j -
              upperRosserFixedDepthMeshRight c m i)
            (c := c)
            (a := upperRosserFixedDepthMeshLeft c m h)
            (b := upperRosserFixedDepthMeshRight c m i)
            hc
            (upperRosserFixedDepthMeshLeft_mem (c := c)
              hc1 m h).1
            (upperRosserFixedDepthMeshRight_le_one (c := c)
              hc1 m i)
      linarith
    have houterComparison : ∀ p₀ ∈ P,
        0 ≤ ∑ i, innerMajorant p₀ i *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1) ∧
        (∑ i, innerMajorant p₀ i *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1)) ≤ outerMajorant (cell p₀) := by
      intro p₀ hp₀
      constructor
      · exact Finset.sum_nonneg fun i _ =>
          mul_nonneg (hinnerMajorantNonneg p₀ i) (hincNonneg i)
      · by_cases hscreen₀ :
          upperRosserFixedDepthMeshRight c m (cell p₀) ≤ r + w
        · have horder :
              upperRosserFixedDepthMeshLeft c m h ≤
                upperRosserFixedDepthMeshRight c m (cell p₀) := by
            exact hqcell.1.trans <| (by
              have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
              have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
              have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
              have hlog : Real.log q ≤ Real.log p₀ :=
                Real.strictMonoOn_log.monotoneOn hqpos hp₀pos
                  (by exact_mod_cast hqmin p₀ hp₀)
              exact ((div_le_div_iff_of_pos_right hlogz).2 hlog).trans
                (hcell p₀ hp₀).2)
          have hinner := hInnerZ z hzInnerZ s hsRange h (cell p₀) a hqcell horder
            (by
              intro i
              exact hinnerCornerBound (cell p₀) i)
          have hsumEq :
              (∑ i, innerMajorant p₀ i *
                (upperRosserFixedDepthMeshRight c m i /
                    upperRosserFixedDepthMeshLeft c m i *
                  (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                    Real.log z)) - 1)) =
                ∑ i,
                  (if upperRosserFixedDepthMeshLeft c m i <
                      upperRosserFixedDepthMeshRight c m (cell p₀) then
                    LinearSieve.upperRosserBoundaryMassAux (k + 1)
                      (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
                        upperRosserFixedDepthMeshRight c m i)
                      (upperRosserFixedDepthMeshLeft c m h)
                      (upperRosserFixedDepthMeshRight c m i) + ε
                  else 0) *
                    (upperRosserFixedDepthMeshRight c m i /
                        upperRosserFixedDepthMeshLeft c m i *
                      (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                        Real.log z)) - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [innerMajorant]
            by_cases hiorder :
                upperRosserFixedDepthMeshLeft c m i <
                  upperRosserFixedDepthMeshRight c m (cell p₀)
            · rw [if_pos ⟨hscreen₀, hiorder⟩, if_pos hiorder]
            · rw [if_neg (fun h => hiorder h.2), if_neg hiorder]
          rw [hsumEq]
          have houterEq : outerMajorant (cell p₀) =
              (∫ x in Set.Ioo a
                  (upperRosserFixedDepthMeshRight c m (cell p₀)),
                x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                  (s - upperRosserFixedDepthMeshRight c m (cell p₀) - x)
                  a x) + E := by
            dsimp [outerMajorant]
            rw [if_pos hscreen₀]
          rw [houterEq]
          convert hinner using 1
          all_goals (norm_num [E, A, w]; ring)
        · have hzero : innerMajorant p₀ = 0 := by
            funext i
            dsimp [innerMajorant]
            rw [if_neg (fun h => hscreen₀ h.1)]
          have houtzero : outerMajorant (cell p₀) = 0 := by
            dsimp [outerMajorant]
            rw [if_neg hscreen₀]
          rw [hzero, houtzero]
          simp
    have houterBound : ∀ p₀ ∈ P,
        (∑ i, innerMajorant p₀ i *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1)) ≤ c⁻¹ * A + CInner := by
      intro p₀ hp₀
      refine (houterComparison p₀ hp₀).2.trans ?_
      by_cases hscreen₀ :
          upperRosserFixedDepthMeshRight c m (cell p₀) ≤ r + w
      · have hint :=
          LinearSieve.integral_inv_mul_upperRosserBoundaryMassAux_le
          (k + 1)
            (s := s)
            (x₀ := upperRosserFixedDepthMeshRight
              c m (cell p₀))
            haPos
              (upperRosserFixedDepthMeshRight_le_one (c := c)
                hc1 m (cell p₀))
        have hainv : a⁻¹ ≤ c⁻¹ := (inv_le_inv₀ haPos hc).2 ha
        have hcinvNonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
        have hsquare : a⁻¹ * a⁻¹ ≤ c⁻¹ * c⁻¹ :=
          mul_le_mul hainv hainv (inv_nonneg.mpr haPos.le) hcinvNonneg
        have hpow : (a⁻¹ * a⁻¹) ^ (k + 1) ≤ A := by
          dsimp [A]
          exact pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr haPos.le)
            (inv_nonneg.mpr haPos.le)) hsquare (k + 1)
        have hint' :
            (∫ x in Set.Ioo a
                (upperRosserFixedDepthMeshRight c m (cell p₀)),
              x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m (cell p₀) - x)
                a x) ≤ c⁻¹ * A :=
          hint.trans (mul_le_mul hainv hpow
            (pow_nonneg (mul_nonneg (inv_nonneg.mpr haPos.le)
              (inv_nonneg.mpr haPos.le)) _) hcinvNonneg)
        dsimp [outerMajorant]
        rw [if_pos hscreen₀]
        exact add_le_add hint' <|
          hEbound.trans (by
            simpa using mul_le_mul_of_nonneg_right hεone hCInner)
      · rw [show outerMajorant (cell p₀) = 0 by
          dsimp [outerMajorant]
          rw [if_neg hscreen₀]]
        positivity
    have hinnerActual : ∀ p₀ ∈ P, ∀ p₁ ∈
        P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
        LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
            a (Real.log p₁ / Real.log z) ≤
          innerMajorant p₀ (cell p₁) := by
      intro p₀ hp₀ p₁ hp₁
      have hp₁data := Finset.mem_filter.mp hp₁
      have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
      have hp₁prime : p₁.Prime :=
        Nat.prime_of_mem_primeFactors (hP hp₁data.1)
      have hqp₀ : q < p₀ := lt_of_le_of_ne (hqmin p₀ hp₀) (by
        intro heq
        apply hqs
        simpa [heq] using hp₀)
      have hp₀screen :=
        upperRosserBoundaryPair_outerLogCoordinate_mem hz1 hΔ hs hqprime
          hp₀prime hqp₀ hp₁data.2.2 (hupper p₀ hp₀)
      have houterScreen :
          upperRosserFixedDepthMeshRight c m (cell p₀) ≤ r + w := by
        have hright :
            upperRosserFixedDepthMeshRight c m (cell p₀) =
              upperRosserFixedDepthMeshLeft c m (cell p₀) + w := by
          rfl
        rw [hright]
        linarith [(hcell p₀ hp₀).1, hp₀screen.1.2]
      have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
      have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
      have hcoord :
          Real.log p₁ / Real.log z < Real.log p₀ / Real.log z := by
        apply (div_lt_div_iff_of_pos_right hlogz).2
        exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
          (by exact_mod_cast hp₁data.2.1)
      have hinnerOrder :
          upperRosserFixedDepthMeshLeft c m (cell p₁) <
            upperRosserFixedDepthMeshRight c m (cell p₀) :=
        (hcell p₁ hp₁data.1).1.trans_lt (hcoord.trans_le (hcell p₀ hp₀).2)
      have hcorner := hCorner m hmCorner s hsRange h (cell p₁) (cell p₀)
        a (Real.log p₀ / Real.log z) (Real.log p₁ / Real.log z)
        hqcell (hcell p₀ hp₀) (hcell p₁ hp₁data.1)
      have hinnerEq : innerMajorant p₀ (cell p₁) =
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
              upperRosserFixedDepthMeshRight c m (cell p₁))
            (upperRosserFixedDepthMeshLeft c m h)
            (upperRosserFixedDepthMeshRight c m (cell p₁)) + ε := by
        dsimp [innerMajorant]
        rw [if_pos ⟨houterScreen, hinnerOrder⟩]
      rw [hinnerEq]
      exact hcorner
    have hinnerActualBound : ∀ p₀ ∈ P, ∀ p₁ ∈
        P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
        LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
            a (Real.log p₁ / Real.log z) ≤ A := by
      intro p₀ hp₀ p₁ hp₁
      have hp₁P := (Finset.mem_filter.mp hp₁).1
      simpa [A] using
        LinearSieve.upperRosserBoundaryMassAux_le_of_lower_bound
          (k + 1) (c := c) hc ha ((hupper p₁ hp₁P).le.trans hb)
    have hpowCell : ∀ p ∈ P,
        z ^ upperRosserFixedDepthMeshLeft c m (cell p) ≤ (p : ℝ) ∧
          (p : ℝ) ≤
            z ^ upperRosserFixedDepthMeshRight c m (cell p) := by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have heq : z ^ (Real.log p / Real.log z) = (p : ℝ) := by
        simpa [Real.logb] using
          Real.rpow_logb (x := (p : ℝ)) hzpos (ne_of_gt hz1) hppos
      exact ⟨calc
          z ^ upperRosserFixedDepthMeshLeft c m (cell p) ≤
              z ^ (Real.log p / Real.log z) :=
            Real.rpow_le_rpow_of_exponent_le hz1.le (hcell p hp).1
          _ = (p : ℝ) := heq,
        calc
          (p : ℝ) = z ^ (Real.log p / Real.log z) := heq.symm
          _ ≤ z ^ upperRosserFixedDepthMeshRight c m (cell p) :=
            Real.rpow_le_rpow_of_exponent_le hz1.le (hcell p hp).2⟩
    have htwo := hTwo S z Δ s ε c s₁ q P
      (fun _ p₁ => cell p₁)
      (upperRosserFixedDepthMeshLeft c m)
      (upperRosserFixedDepthMeshRight c m)
      innerMajorant cell
      (upperRosserFixedDepthMeshLeft c m)
      (upperRosserFixedDepthMeshRight c m)
      outerMajorant hzTwoZ hΔ hlocal hs hsRange.2 hqprime hqs hP hqmin hcut
      hc1.le hzc hε.le hscreen hqa hcomparison
      (fun i => (upperRosserFixedDepthMeshLeft_mem hc1 m i).1)
      (fun i => upperRosserFixedDepthMeshLeft_le_right hc1 m i)
      (by
        intro p₀ hp₀ p₁ hp₁
        exact hpowCell p₁ (Finset.mem_filter.mp hp₁).1)
      (fun p₀ _ i => hinnerMajorantNonneg p₀ i) hinnerActual hinnerActualBound
      (fun j => (upperRosserFixedDepthMeshLeft_mem hc1 m j).1)
      (fun j => upperRosserFixedDepthMeshLeft_le_right hc1 m j)
      hpowCell houterMajorantNonneg houterComparison houterBound
    have houter := hOuterZ z hzOuterZ s hsRange a ⟨ha, ha1⟩ b hb har
    have hinc := hInc z hzIncZ
    have hbaseOuter :
        ∑ j : Fin (m + 1),
            (if upperRosserFixedDepthMeshRight c m j ≤ r + w then
              ∫ x in Set.Ioo a
                (upperRosserFixedDepthMeshRight c m j),
                x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                  (s - upperRosserFixedDepthMeshRight c m j - x) a x
            else 0) *
              (upperRosserFixedDepthMeshRight c m j /
                  upperRosserFixedDepthMeshLeft c m j *
                (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                  Real.log z)) - 1) ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 2) s a b +
            ε * COuter := by
      have houter' := houter
      have hwidthLe : w ≤ ε := hwidth.le
      have haInv : a⁻¹ ≤ c⁻¹ := (inv_le_inv₀ haPos hc).2 ha
      have hcInvNonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
      have haSq : a⁻¹ * a⁻¹ ≤ c⁻¹ * c⁻¹ :=
        mul_le_mul haInv haInv (inv_nonneg.mpr haPos.le) hcInvNonneg
      have hpowA₂ : (a⁻¹ * a⁻¹) ^ (k + 2) ≤ A₂ := by
        dsimp [A₂]
        exact pow_le_pow_left₀
          (mul_nonneg (inv_nonneg.mpr haPos.le) (inv_nonneg.mpr haPos.le))
          haSq (k + 2)
      have hA₂w : (a⁻¹ * a⁻¹) ^ (k + 2) * w ≤ A₂ * ε :=
        calc
          (a⁻¹ * a⁻¹) ^ (k + 2) * w ≤ A₂ * w :=
            mul_le_mul_of_nonneg_right hpowA₂
              (upperRosserFixedDepthMeshWidth_pos hc1 m).le
          _ ≤ A₂ * ε := mul_le_mul_of_nonneg_left hwidthLe hA₂
      have hAw : A * w ≤ A * ε := mul_le_mul_of_nonneg_left hwidthLe hA
      have hcInvAw : c⁻¹ * A * w ≤ c⁻¹ * A * ε := by
        calc
          c⁻¹ * A * w = c⁻¹ * (A * w) := by ring
          _ ≤ c⁻¹ * (A * ε) := mul_le_mul_of_nonneg_left hAw hcInvNonneg
          _ = c⁻¹ * A * ε := by ring
      have hcSq : 0 < c ^ 2 := sq_pos_of_pos hc
      have hcInvAwDiv : c⁻¹ * A * w / c ^ 2 ≤ c⁻¹ * A * ε / c ^ 2 :=
        div_le_div_of_nonneg_right hcInvAw hcSq.le
      dsimp [COuter]
      calc
        _ ≤ LinearSieve.upperRosserBoundaryMassAux (k + 2) s a b +
            (a⁻¹ * a⁻¹) ^ (k + 2) * w + ε / c +
              c⁻¹ * A * w / c ^ 2 + ε := by
          simpa [r, w, A] using houter'
        _ ≤ LinearSieve.upperRosserBoundaryMassAux (k + 2) s a b +
            A₂ * ε + ε / c + c⁻¹ * A * w / c ^ 2 + ε := by
          linarith
        _ ≤ LinearSieve.upperRosserBoundaryMassAux (k + 2) s a b +
            A₂ * ε + ε / c + c⁻¹ * A * ε / c ^ 2 + ε := by
          linarith
        _ = LinearSieve.upperRosserBoundaryMassAux (k + 2) s a b +
            ε * (A₂ + 1 / c + c⁻¹ * A / c ^ 2 + 1) := by ring
    have houterSum :
        (∑ j : Fin (m + 1), outerMajorant j *
          (upperRosserFixedDepthMeshRight c m j /
              upperRosserFixedDepthMeshLeft c m j *
            (1 + K / (upperRosserFixedDepthMeshLeft c m j *
              Real.log z)) - 1)) ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 2) s a b +
            ε * (COuter + (c⁻¹ + 1) * CInner) := by
      have hsum :
          (∑ j : Fin (m + 1), outerMajorant j *
            (upperRosserFixedDepthMeshRight c m j /
                upperRosserFixedDepthMeshLeft c m j *
              (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                Real.log z)) - 1)) ≤
            (∑ j : Fin (m + 1),
              (if upperRosserFixedDepthMeshRight c m j ≤ r + w then
                ∫ x in Set.Ioo a
                  (upperRosserFixedDepthMeshRight c m j),
                  x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                    (s - upperRosserFixedDepthMeshRight c m j - x) a x
              else 0) *
                (upperRosserFixedDepthMeshRight c m j /
                    upperRosserFixedDepthMeshLeft c m j *
                  (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                    Real.log z)) - 1)) +
              E * (∑ j : Fin (m + 1),
                (upperRosserFixedDepthMeshRight c m j /
                    upperRosserFixedDepthMeshLeft c m j *
                  (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                    Real.log z)) - 1)) := by
        calc
          _ ≤ ∑ j : Fin (m + 1),
              ((if upperRosserFixedDepthMeshRight c m j ≤ r + w then
                  ∫ x in Set.Ioo a
                    (upperRosserFixedDepthMeshRight c m j),
                    x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                      (s - upperRosserFixedDepthMeshRight c m j - x) a x
                else 0) *
                  (upperRosserFixedDepthMeshRight c m j /
                      upperRosserFixedDepthMeshLeft c m j *
                    (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                      Real.log z)) - 1) +
                E * (upperRosserFixedDepthMeshRight c m j /
                      upperRosserFixedDepthMeshLeft c m j *
                    (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                      Real.log z)) - 1)) := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hscreenj :
                upperRosserFixedDepthMeshRight c m j ≤ r + w
            · rw [show outerMajorant j =
                  (∫ x in Set.Ioo a
                      (upperRosserFixedDepthMeshRight c m j),
                    x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                      (s - upperRosserFixedDepthMeshRight c m j - x)
                      a x) + E by
                    dsimp [outerMajorant]
                    rw [if_pos hscreenj]]
              rw [if_pos hscreenj]
              let I : ℝ :=
                ∫ x in Set.Ioo a
                    (upperRosserFixedDepthMeshRight c m j),
                  x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1)
                    (s - upperRosserFixedDepthMeshRight c m j - x)
                    a x
              let d : ℝ :=
                upperRosserFixedDepthMeshRight c m j /
                    upperRosserFixedDepthMeshLeft c m j *
                  (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                    Real.log z)) - 1
              change (I + E) * d ≤ I * d + E * d
              rw [add_mul]
            · rw [show outerMajorant j = 0 by
                    dsimp [outerMajorant]
                    rw [if_neg hscreenj]]
              rw [if_neg hscreenj]
              simpa using mul_nonneg hE (hincNonneg j)
          _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      have hinc' :
          (∑ j : Fin (m + 1),
              (upperRosserFixedDepthMeshRight c m j /
                  upperRosserFixedDepthMeshLeft c m j *
                (1 + K / (upperRosserFixedDepthMeshLeft c m j *
                 Real.log z)) - 1)) ≤ c⁻¹ + ε := by
        simpa using hinc
      have hEinc : E * (∑ j : Fin (m + 1),
          (upperRosserFixedDepthMeshRight c m j /
              upperRosserFixedDepthMeshLeft c m j *
            (1 + K / (upperRosserFixedDepthMeshLeft c m j *
              Real.log z)) - 1)) ≤ ε * CInner * (c⁻¹ + 1) := by
        calc
          E * _ ≤ E * (c⁻¹ + ε) := mul_le_mul_of_nonneg_left hinc' hE
          _ ≤ (ε * CInner) * (c⁻¹ + ε) :=
            mul_le_mul_of_nonneg_right hEbound (by positivity)
          _ ≤ ε * CInner * (c⁻¹ + 1) := by
            have hεBound : c⁻¹ + ε ≤ c⁻¹ + 1 := by linarith
            exact mul_le_mul_of_nonneg_left hεBound
              (mul_nonneg hε.le hCInner)
      linarith
    let R : ℝ := Real.log (z + 1) / Real.log (z ^ c) *
      (1 + K / Real.log (z ^ c)) - 1
    have hR := hFactor z hzFactorZ
    have hfour : 1 ≤ 4 / c := by
      apply (le_div_iff₀ hc).2
      linarith
    have hRsq : R ^ 2 ≤ (4 / c) ^ 2 := by
      have hprod : 0 ≤ (4 / c - R) * (R + 4 / c) :=
        mul_nonneg (by dsimp [R] at hR ⊢; linarith)
          (by dsimp [R] at hR ⊢; linarith [hfour])
      nlinarith
    dsimp [a] at houterSum ⊢
    have hRlinear :
        ε * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) ≤ (4 / c) * ε :=
      by simpa [mul_comm] using mul_le_mul_of_nonneg_left hR.2 hε.le
    have hRquadratic :
        ε * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) ^ 2 ≤ (4 / c) ^ 2 * ε := by
      dsimp [R] at hRsq
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hRsq hε.le
    nlinarith
  · have hprime : ∀ p ∈ P, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hP hp)
    rw [show k + 2 = (k + 1) + 1 by omega,
      LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_succ
        (fun p => S.nu p / (1 - S.nu p)) hqs hqprime hprime hqmin (k + 1)]
    have hempty : ∀ p₀ ∈ P,
        P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1) = ∅ := by
      intro p₀ hp₀
      apply Finset.filter_eq_empty_iff.mpr
      intro p₁ hp₁ hp₁data
      have hp₀prime : p₀.Prime := hprime p₀ hp₀
      have hqp₀ : q < p₀ := lt_of_le_of_ne (hqmin p₀ hp₀) (by
        intro heq
        apply hqs
        simpa [heq] using hp₀)
      have hp₀screen :=
        upperRosserBoundaryPair_outerLogCoordinate_mem hz1 hΔ hs hqprime
          hp₀prime hqp₀ hp₁data.2 (hupper p₀ hp₀)
      exact har (hp₀screen.1.1.le.trans hp₀screen.1.2)
    have hzero :
        (∑ p₀ ∈ P, ∑ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p))
              ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q
              (P.filter fun p => p < p₁) (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro p₀ hp₀
      rw [hempty p₀ hp₀]
      simp
    rw [hzero]
    exact add_nonneg
      (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 2) haPos.le) hρ.le

/-- Fixed-depth screened residual comparisons are uniform above a cutoff that
depends only on the depth, the local-product constant, the requested error, and
the upper end of the level range.  The distinguished prime and inherited face
remain arbitrary. -/
theorem exists_upperRosserBoundaryScreenedResidualComparison_of_lt_one
    (k : ℕ) (K ρ c s₁ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hc : 0 < c) (hc1 : c < 1) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (q : ℕ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        UpperRosserBoundaryScreenedResidualComparison S z q k ρ c s₁ := by
  induction k generalizing K ρ s₁ with
  | zero =>
      refine ⟨2, le_rfl, ?_⟩
      intro S z q hz _hlocal
      have hzero :=
        upperRosserBoundaryScreenedResidualComparison_zero
          (c := c) (s₁ := s₁) (q := q) S (lt_of_lt_of_le (by norm_num) hz)
      intro Δ s b P hΔ hs hsUpper hP hqs hqprime hprime hqmin hupper
        hqscreen hb
      calc
        _ ≤ LinearSieve.upperRosserBoundaryMassAux 0 s
              (Real.log q / Real.log z) b + 0 :=
          hzero hΔ hs hsUpper hP hqs hqprime hprime hqmin hupper hqscreen hb
        _ ≤ LinearSieve.upperRosserBoundaryMassAux 0 s
              (Real.log q / Real.log z) b + ρ := by linarith
  | succ k ih =>
      cases k with
      | zero =>
          obtain ⟨z₀, hz₀, hone⟩ :=
            exists_upperRosserBoundaryChainsFixedDepthDensity_one_le_boundaryMassAux_add_screened
              K ρ c hK hρ hc hc1
          refine ⟨z₀, hz₀, ?_⟩
          intro S z q hz hlocal Δ s b P hΔ hs _hsUpper hP hqs hqprime _hprime
            hqmin hupper hqscreen hb
          exact hone S z Δ s b q P hz (by linarith) hlocal hs hqprime hqs hP
            hqmin hupper hqscreen hb
      | succ k =>
          obtain ⟨ε, hε, zStep, hzStep, hstep⟩ :=
            exists_upperRosserBoundaryChainsFixedDepthDensity_succ_succ_le_boundaryMassAux_add
              k K ρ c 0 s₁ hK hρ hc hc1
          obtain ⟨zIH, hzIH, hIH⟩ := ih K ε s₁ hK hε
          let z₀ := max zStep zIH
          refine ⟨z₀, hzStep.trans (le_max_left _ _), ?_⟩
          intro S z q hz hlocal
          have hzStepZ : zStep ≤ z := (le_max_left _ _).trans hz
          have hzIHZ : zIH ≤ z := (le_max_right _ _).trans hz
          have hcomparison :
              UpperRosserBoundaryScreenedResidualComparison
                S z q (k + 1) ε c s₁ :=
            hIH S z q hzIHZ hlocal
          intro Δ s b P hΔ hs hsUpper hP hqs hqprime hprime hqmin hupper
            hqscreen hb
          have hz1 : 1 < z :=
            lt_of_lt_of_le (by norm_num) (hzStep.trans hzStepZ)
          have hspos : 0 < s := by
            rw [hs]
            exact div_pos (Real.log_pos hΔ) (Real.log_pos hz1)
          exact hstep S z Δ s b q P hzStepZ (by linarith) hlocal hs
            ⟨hspos.le, hsUpper⟩ hqprime hqs hP hqmin hupper hqscreen hb
            hcomparison

end MathlibNt.SieveTheory.SwitchingPrinciple
