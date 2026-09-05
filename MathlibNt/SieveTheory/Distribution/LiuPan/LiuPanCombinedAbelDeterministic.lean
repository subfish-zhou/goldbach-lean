import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The deterministic term in Liu's aggregate Abel reduction

The discrete Abel main term is an ordinary right Riemann sum for `1 / log`.
Above `2` monotonicity gives a uniform error.  Below `2` the integral is kept
explicit, so the singular contribution is not silently treated as an ordinary
Riemann sum.  Liu's product-cube support gives the exact `O(N^(2/3))` indicator
mass needed for a subsequent modulus average.
-/

open scoped Asymptotics BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset MeasureTheory intervalIntegral
open AnalyticNumberTheory.Sieve

private noncomputable def inverseLogDensity (x : ℝ) : ℝ :=
  1 / Real.log x

private lemma inverseLogDensity_antitoneOn :
    AntitoneOn inverseLogDensity (Set.Ici (2 : ℝ)) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  unfold inverseLogDensity
  exact one_div_le_one_div_of_le
    (Real.log_pos (by linarith))
    (Real.log_le_log (by linarith) hxy)

lemma liuPanDiscreteInverseLogMain_succ (m : ℕ) (hm : 2 ≤ m) :
    liuPanDiscreteInverseLogMain (m + 1) =
      liuPanDiscreteInverseLogMain m + 1 / Real.log (m + 1 : ℕ) := by
  unfold liuPanDiscreteInverseLogMain
  rw [Finset.sum_range_succ]
  simp only [liuPanInverseLogAbelWeight, if_pos hm]
  push_cast
  ring

/-- Exact telescoping formula for the discrete Abel main term. -/
theorem liuPanDiscreteInverseLogMain_eq_sum (m : ℕ) :
    liuPanDiscreteInverseLogMain m =
      if 2 ≤ m then
        2 / Real.log 2 +
          ∑ n ∈ Ico 3 (m + 1), 1 / Real.log (n : ℝ)
      else 0 := by
  by_cases hm : 2 ≤ m
  · rw [if_pos hm]
    induction m, hm using Nat.le_induction with
    | base =>
        unfold liuPanDiscreteInverseLogMain
        simp only [Ico_self, sum_empty, add_zero]
        have hzero :
            (∑ x ∈ range 2, liuPanInverseLogAbelWeight x * (x : ℝ)) = 0 := by
          apply sum_eq_zero
          intro n hn
          have hnlt : n < 2 := mem_range.mp hn
          simp [liuPanInverseLogAbelWeight, show ¬2 ≤ n by omega]
        rw [hzero, add_zero]
        ring
    | succ m hm ih =>
        rw [liuPanDiscreteInverseLogMain_succ m hm, ih,
          sum_Ico_succ_top (by omega : 3 ≤ m + 1)]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  · rw [if_neg hm]
    interval_cases m <;>
      simp [liuPanDiscreteInverseLogMain, liuPanInverseLogAbelWeight]

private lemma inverseLogDensity_sum_le_integral
    {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Ico 3 (Nat.floor x + 1), inverseLogDensity n) ≤
      ∫ t in (2 : ℝ)..x, inverseLogDensity t := by
  have hm : 2 ≤ Nat.floor x :=
    (Nat.le_floor_iff (by positivity)).2 hx
  have hanti : AntitoneOn inverseLogDensity
      (Set.Icc (2 : ℝ) (Nat.floor x : ℝ)) :=
    inverseLogDensity_antitoneOn.mono fun _ ht => ht.1
  have hsum := hanti.sum_le_integral_Ico hm
  have hmx : (Nat.floor x : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hint : IntervalIntegrable inverseLogDensity volume 2 x := by
    change IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x
    exact liuLogarithmicIntegrand_intervalIntegrable hx
  calc
    (∑ n ∈ Ico 3 (Nat.floor x + 1), inverseLogDensity n) =
        ∑ n ∈ Ico 2 (Nat.floor x), inverseLogDensity (n + 1) := by
          apply sum_bij (fun n _ => n - 1)
          · intro n hn
            simp only [mem_Ico] at hn ⊢
            omega
          · intro a₁ ha₁ a₂ ha₂ h
            simp only [mem_Ico] at ha₁ ha₂
            omega
          · intro b hb
            simp only [mem_Ico] at hb
            refine ⟨b + 1, ?_, by omega⟩
            simp only [mem_Ico]
            omega
          · intro n hn
            simp only [mem_Ico] at hn
            have heq : n - 1 + 1 = n := by omega
            have heqR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
              exact_mod_cast heq
            rw [heqR]
    _ ≤ ∫ t in (2 : ℝ)..(Nat.floor x : ℝ), inverseLogDensity t := by
      convert hsum using 1 <;> norm_num [Nat.cast_add]
    _ ≤ ∫ t in (2 : ℝ)..x, inverseLogDensity t := by
      have hmR : (2 : ℝ) ≤ Nat.floor x := by exact_mod_cast hm
      have hint₁ : IntervalIntegrable inverseLogDensity volume 2 (Nat.floor x) := by
        change IntervalIntegrable (fun t : ℝ => 1 / Real.log t)
          volume 2 (Nat.floor x)
        exact liuLogarithmicIntegrand_intervalIntegrable_of_two_le (le_refl 2) hmR
      have hint₂ : IntervalIntegrable inverseLogDensity volume (Nat.floor x) x := by
        change IntervalIntegrable (fun t : ℝ => 1 / Real.log t)
          volume (Nat.floor x) x
        exact liuLogarithmicIntegrand_intervalIntegrable_of_two_le hmR hmx
      calc
        (∫ t in (2 : ℝ)..(Nat.floor x : ℝ), inverseLogDensity t) ≤
            (∫ t in (2 : ℝ)..(Nat.floor x : ℝ), inverseLogDensity t) +
              ∫ t in (Nat.floor x : ℝ)..x, inverseLogDensity t :=
          le_add_of_nonneg_right
            (integral_nonneg hmx fun t ht => by
              unfold inverseLogDensity
              exact liuLogarithmicIntegrand_nonneg (hmR.trans ht.1))
        _ = ∫ t in (2 : ℝ)..x, inverseLogDensity t :=
          integral_add_adjacent_intervals hint₁ hint₂

private lemma integral_le_inverseLogDensity_sum_add
    {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, inverseLogDensity t) ≤
      (∑ n ∈ Ico 3 (Nat.floor x + 1), inverseLogDensity n) +
        1 / Real.log 2 := by
  have hm : 2 ≤ Nat.floor x :=
    (Nat.le_floor_iff (by positivity)).2 hx
  by_cases hm3 : 3 ≤ Nat.floor x
  · have hmx : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmx' : x ≤ ((Nat.floor x + 1 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact hmx.le
    have hx3 : 3 ≤ x := by
      exact (show (3 : ℝ) ≤ Nat.floor x by exact_mod_cast hm3).trans
        (Nat.floor_le (by positivity))
    have hanti : AntitoneOn inverseLogDensity
        (Set.Icc (3 : ℝ) (Nat.floor x + 1 : ℕ)) :=
        inverseLogDensity_antitoneOn.mono fun _ ht =>
          (by norm_num : (2 : ℝ) ≤ 3).trans ht.1
    have hint23 : IntervalIntegrable inverseLogDensity volume 2 3 := by
        change IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 3
        exact liuLogarithmicIntegrand_intervalIntegrable_of_two_le
          (le_refl 2) (by norm_num)
    have hint3x : IntervalIntegrable inverseLogDensity volume 3 x := by
        change IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 3 x
        exact liuLogarithmicIntegrand_intervalIntegrable_of_two_le
          (by norm_num) hx3
    calc
      (∫ t in (2 : ℝ)..x, inverseLogDensity t) =
          (∫ t in (2 : ℝ)..3, inverseLogDensity t) +
            ∫ t in (3 : ℝ)..x, inverseLogDensity t :=
        (integral_add_adjacent_intervals hint23 hint3x).symm
      _ ≤ 1 / Real.log 2 +
          ∫ t in (3 : ℝ)..x, inverseLogDensity t := by
        gcongr
        calc
          (∫ t in (2 : ℝ)..3, inverseLogDensity t) ≤
              ∫ _t in (2 : ℝ)..3, 1 / Real.log 2 := by
            apply integral_mono_on (by norm_num) hint23 intervalIntegrable_const
            intro t ht
            exact one_div_le_one_div_of_le
              (Real.log_pos (by norm_num))
              (Real.log_le_log (by norm_num) ht.1)
          _ = 1 / Real.log 2 := by
            rw [intervalIntegral.integral_const]
            norm_num [smul_eq_mul]
      _ ≤ 1 / Real.log 2 +
          ∫ t in (3 : ℝ)..(Nat.floor x + 1 : ℕ),
            inverseLogDensity t := by
        gcongr
        have hintx : IntervalIntegrable inverseLogDensity volume x
            (Nat.floor x + 1 : ℕ) := by
          change IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume x
            (Nat.floor x + 1 : ℕ)
          exact liuLogarithmicIntegrand_intervalIntegrable_of_two_le hx hmx'
        calc
          (∫ t in (3 : ℝ)..x, inverseLogDensity t) ≤
              (∫ t in (3 : ℝ)..x, inverseLogDensity t) +
                ∫ t in x..(Nat.floor x + 1 : ℕ), inverseLogDensity t :=
            le_add_of_nonneg_right
              (integral_nonneg hmx' fun t ht => by
                unfold inverseLogDensity
                exact liuLogarithmicIntegrand_nonneg (hx.trans ht.1))
          _ = ∫ t in (3 : ℝ)..(Nat.floor x + 1 : ℕ),
                inverseLogDensity t :=
            integral_add_adjacent_intervals hint3x hintx
      _ ≤ 1 / Real.log 2 +
          ∑ n ∈ Ico 3 (Nat.floor x + 1), inverseLogDensity n := by
        gcongr
        exact hanti.integral_le_sum_Ico
          (by exact_mod_cast (show 3 ≤ Nat.floor x + 1 by omega))
      _ = _ := by ring
  · have hm_eq : Nat.floor x = 2 := by omega
    have hx3 : x ≤ 3 := by
      have h := (Nat.lt_floor_add_one x).le
      rw [hm_eq] at h
      norm_num at h ⊢
      exact h
    simp only [hm_eq, Ico_self, sum_empty, zero_add]
    have hint : IntervalIntegrable inverseLogDensity volume 2 x := by
      change IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x
      exact liuLogarithmicIntegrand_intervalIntegrable hx
    calc
      (∫ t in (2 : ℝ)..x, inverseLogDensity t) ≤
          ∫ _t in (2 : ℝ)..x, 1 / Real.log 2 := by
        apply integral_mono_on hx hint intervalIntegrable_const
        intro t ht
        exact one_div_le_one_div_of_le
          (Real.log_pos (by norm_num))
          (Real.log_le_log (by norm_num) ht.1)
      _ = (x - 2) / Real.log 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ 1 / Real.log 2 := by
        exact (div_le_div_iff_of_pos_right
          (Real.log_pos (by norm_num))).2 (by linarith)

/-- Above the logarithmic singularity, the discrete Abel main term differs from
the normalized logarithmic integral by a constant independent of `x`. -/
theorem abs_liuPanDiscreteInverseLogMain_floor_sub_liuLogarithmicIntegral_le_of_two_le
    (kappa x : ℝ) (hx : 2 ≤ x) :
    |liuPanDiscreteInverseLogMain (Nat.floor x) -
        liuLogarithmicIntegral kappa x| ≤
      |kappa| + 3 / Real.log 2 := by
  have hm : 2 ≤ Nat.floor x :=
    (Nat.le_floor_iff (by positivity)).2 hx
  rw [liuPanDiscreteInverseLogMain_eq_sum, if_pos hm]
  change |2 / Real.log 2 +
      (∑ n ∈ Ico 3 (Nat.floor x + 1), inverseLogDensity n) -
      (kappa + ∫ t in (2 : ℝ)..x, inverseLogDensity t)| ≤ _
  have hlo := inverseLogDensity_sum_le_integral hx
  have hhi := integral_le_inverseLogDensity_sum_add hx
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hrecip : 0 < 1 / Real.log (2 : ℝ) := one_div_pos.mpr hlog2
  simp only [div_eq_mul_inv] at *
  rw [abs_le]
  constructor <;> linarith [le_abs_self kappa, neg_le_abs kappa]

/-- The rational source arguments use the same integer endpoint as Euclidean
division.  This keeps the singular `x < 2` regime visibly separate from the
ordinary Riemann-sum comparison above. -/
theorem floor_natCast_div_natCast_eq_div (y a : ℕ) :
    Nat.floor ((y : ℝ) / (a : ℝ)) = y / a := by
  simpa using (Nat.floor_div_eq_div y a : Nat.floor ((y : ℝ) / a) = y / a)

private lemma sub_one_inv_isBigO_inverseLogDensity :
    (fun t : ℝ => (t - 1)⁻¹) =O[nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ]
      (fun t : ℝ => 1 / Real.log t) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds
        (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))] with
    t htne ht
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : t ≠ 1 := by simpa using htne
  have hsub : 0 < |t - 1| := abs_pos.mpr (sub_ne_zero.mpr ht1)
  have hlog : 0 < |Real.log t| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one ht0 ht1)
  have hbound : |Real.log t| ≤ 2 * |t - 1| := by
    by_cases h1t : 1 ≤ t
    · rw [abs_of_nonneg (Real.log_nonneg h1t),
        abs_of_nonneg (sub_nonneg.mpr h1t)]
      linarith [Real.log_le_sub_one_of_pos ht0]
    · have htlt : t < 1 := lt_of_not_ge h1t
      rw [abs_of_neg (Real.log_neg ht0 htlt), abs_of_neg (sub_neg.mpr htlt)]
      have hinv : Real.log t⁻¹ ≤ t⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
      rw [Real.log_inv] at hinv
      have hinv_le : t⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ ht0 (by norm_num : (0 : ℝ) < 2)]
        linarith [ht.1]
      calc
        -Real.log t ≤ t⁻¹ - 1 := hinv
        _ = t⁻¹ * (1 - t) := by field_simp [ht0.ne']
        _ ≤ 2 * (1 - t) :=
          mul_le_mul_of_nonneg_right hinv_le (by linarith)
        _ = 2 * -(t - 1) := by ring
  rw [norm_inv, Real.norm_eq_abs, norm_div, norm_one, Real.norm_eq_abs]
  field_simp [ne_of_gt hsub, ne_of_gt hlog]
  simpa [mul_comm] using hbound

/-- Mathlib's interval integral is zero when the interval crosses the
non-integrable logarithmic singularity at `1`. -/
lemma integral_inverseLogDensity_eq_zero_of_le_one
    {x : ℝ} (hx : x ≤ 1) :
    (∫ t in (2 : ℝ)..x, 1 / Real.log t) = 0 := by
  apply intervalIntegral.integral_undef
  apply not_intervalIntegrable_of_sub_inv_isBigO_punctured
    sub_one_inv_isBigO_inverseLogDensity
  · linarith
  · simp [Set.mem_uIcc, hx]

/-- On the integrable side of the singularity, the short integral grows at
most logarithmically in the reciprocal distance from `1`. -/
lemma abs_integral_inverseLogDensity_le_log_inv_sub_one
    {x : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) :
    |∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
      2 * Real.log (1 / (x - 1)) := by
  have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume x 2 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      rw [Set.uIcc_of_le hx2] at ht
      exact ne_of_gt (Real.log_pos (lt_of_lt_of_le hx ht.1))
    · exact Real.continuousOn_log.mono fun t ht => by
        rw [Set.uIcc_of_le hx2] at ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [ht.1]
  have hgi : IntervalIntegrable (fun t : ℝ => 2 / (t - 1)) volume x 2 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    rw [Set.uIcc_of_le hx2] at ht
    change t - 1 ≠ 0
    linarith [ht.1]
  have hnonneg : 0 ≤ ∫ t in x..(2 : ℝ), 1 / Real.log t := by
    apply intervalIntegral.integral_nonneg hx2
    intro t ht
    exact one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
  rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hnonneg]
  calc
    (∫ t in x..(2 : ℝ), 1 / Real.log t) ≤
        ∫ t in x..(2 : ℝ), 2 / (t - 1) := by
      apply intervalIntegral.integral_mono_on hx2 hfi hgi
      intro t ht
      have ht1 : 1 < t := lt_of_lt_of_le hx ht.1
      have ht2 : t ≤ 2 := ht.2
      have hlog : 0 < Real.log t := Real.log_pos ht1
      have hsub : 0 < t - 1 := sub_pos.mpr ht1
      apply (div_le_div_iff₀ hlog hsub).2
      simpa only [one_mul] using
        (Real.self_sub_one_le_mul_log (le_of_lt (by linarith : 0 < t))).trans
          (mul_le_mul_of_nonneg_right ht2 (le_of_lt hlog))
    _ = 2 * Real.log (1 / (x - 1)) := by
      have hderiv : ∀ t ∈ Set.uIcc x 2,
          HasDerivAt (fun u : ℝ => 2 * Real.log (u - 1)) (2 / (t - 1)) t := by
        intro t ht
        rw [Set.uIcc_of_le hx2] at ht
        have htne : t - 1 ≠ 0 := by linarith [ht.1]
        have hlogderiv := (Real.hasDerivAt_log htne).comp t
          ((hasDerivAt_id t).sub_const 1)
        simpa only [one_mul, mul_one, id_eq, Pi.sub_apply, Pi.one_apply,
          div_eq_mul_inv, Function.comp_apply] using hlogderiv.const_mul 2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hgi]
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, mul_zero, zero_sub,
        Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (sub_ne_zero.mpr hx.ne')]
      simp

/-- Below the endpoint `2`, the discrete part is zero.  The displayed integral
is the only possible logarithmic singular contribution; no assertion of
interval-integrability through `1` is being made. -/
theorem abs_liuPanDiscreteInverseLogMain_floor_sub_liuLogarithmicIntegral_le_of_nonneg_lt_two
    (kappa x : ℝ) (hx : 0 ≤ x) (hx2 : x < 2) :
    |liuPanDiscreteInverseLogMain (Nat.floor x) -
        liuLogarithmicIntegral kappa x| ≤
      |kappa| + |∫ t in (2 : ℝ)..x, 1 / Real.log t| := by
  have hfloor : Nat.floor x < 2 := by
    rw [Nat.floor_lt (by positivity)]
    exact hx2
  have hmain : liuPanDiscreteInverseLogMain (Nat.floor x) = 0 := by
    rw [liuPanDiscreteInverseLogMain_eq_sum, if_neg (by omega)]
  rw [hmain, liuLogarithmicIntegral]
  rw [show 0 - (kappa + ∫ t in (2 : ℝ)..x, 1 / Real.log t) =
    -(kappa + ∫ t in (2 : ℝ)..x, 1 / Real.log t) by ring, abs_neg]
  exact abs_add_le _ _

/-- A uniform formula for the error on `x ≥ 0`.  The only growing term is the
explicit logarithm of the reciprocal distance to the integrable side of the
singularity at `1`; on the non-integrable side Mathlib's integral is zero. -/
theorem abs_liuPanDiscreteInverseLogMain_floor_sub_liuLogarithmicIntegral_le
    (kappa x : ℝ) (hx : 0 ≤ x) :
    |liuPanDiscreteInverseLogMain (Nat.floor x) -
        liuLogarithmicIntegral kappa x| ≤
      |kappa| + 3 / Real.log 2 +
        if 1 < x ∧ x < 2 then 2 * Real.log (1 / (x - 1)) else 0 := by
  by_cases hx1 : x ≤ 1
  · rw [if_neg (by intro h; linarith [h.1])]
    have hfloor : Nat.floor x < 2 := by
      rw [Nat.floor_lt (by positivity)]
      exact hx1.trans_lt (by norm_num)
    rw [liuPanDiscreteInverseLogMain_eq_sum, if_neg (by omega),
      liuLogarithmicIntegral, integral_inverseLogDensity_eq_zero_of_le_one hx1]
    have hconst : 0 ≤ 3 / Real.log (2 : ℝ) := by positivity
    simpa using
      (le_add_of_nonneg_right hconst : |kappa| ≤ |kappa| + 3 / Real.log 2)
  · have hx1' : 1 < x := lt_of_not_ge hx1
    by_cases hx2 : x < 2
    · rw [if_pos ⟨hx1', hx2⟩]
      have hbase :=
        abs_liuPanDiscreteInverseLogMain_floor_sub_liuLogarithmicIntegral_le_of_nonneg_lt_two
          kappa x hx hx2
      have hnear := abs_integral_inverseLogDensity_le_log_inv_sub_one hx1' hx2.le
      have hconst : 0 ≤ 3 / Real.log (2 : ℝ) := by positivity
      linarith
    · rw [if_neg (by intro h; exact hx2 h.2), add_zero]
      exact
        abs_liuPanDiscreteInverseLogMain_floor_sub_liuLogarithmicIntegral_le_of_two_le
          kappa x (le_of_not_gt hx2)

/-- At rational source arguments the distance from the singularity is either
zero/non-integrable or at least `1/a`, giving a uniform logarithmic bound. -/
theorem abs_liuPanDiscreteInverseLogMain_div_sub_liuLogarithmicIntegral_le
    (kappa : ℝ) (y a : ℕ) :
    |liuPanDiscreteInverseLogMain (y / a) -
        liuLogarithmicIntegral kappa ((y : ℝ) / a)| ≤
      |kappa| + 3 / Real.log 2 + 2 * Real.log (a + 1 : ℕ) := by
  rw [← floor_natCast_div_natCast_eq_div]
  have hglobal :=
    abs_liuPanDiscreteInverseLogMain_floor_sub_liuLogarithmicIntegral_le
      kappa ((y : ℝ) / a) (by positivity)
  apply hglobal.trans
  gcongr
  split_ifs with h
  · rcases h with ⟨h1, h2⟩
    have ha : 0 < a := by
      by_cases ha0 : a = 0
      · exfalso
        have hydiv : (y : ℝ) / (a : ℝ) = 0 := by simp [ha0]
        rw [hydiv] at h1
        norm_num at h1
      · exact Nat.pos_of_ne_zero ha0
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hayR : (a : ℝ) < y := by
      simpa only [one_mul] using (lt_div_iff₀ haR).mp h1
    have hay : a < y := by exact_mod_cast hayR
    have hdiff : 1 ≤ y - a := by omega
    have hdiffR : (1 : ℝ) ≤ (y - a : ℕ) := by exact_mod_cast hdiff
    have hgap : 1 / (a : ℝ) ≤ (y : ℝ) / a - 1 := by
      calc
        1 / (a : ℝ) ≤ (y - a : ℕ) / (a : ℝ) :=
          (div_le_div_iff_of_pos_right haR).2 hdiffR
        _ = (y : ℝ) / a - 1 := by
          rw [Nat.cast_sub hay.le]
          field_simp [haR.ne']
    have hrecip : 1 / ((y : ℝ) / a - 1) ≤ (a : ℝ) := by
      calc
        1 / ((y : ℝ) / a - 1) ≤ 1 / (1 / (a : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hgap
        _ = (a : ℝ) := by field_simp [haR.ne']
    have hlog := Real.log_le_log
      (by positivity : (0 : ℝ) < 1 / ((y : ℝ) / a - 1))
      (hrecip.trans (by norm_num : (a : ℝ) ≤ a + 1))
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  · exact mul_nonneg (by norm_num)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ a + 1 by omega)))

/-- The uniform scalar error used for every source index `a ≤ N`. -/
noncomputable def liuPanInverseLogDeterministicErrorBound
    (kappa : ℝ) (N : ℕ) : ℝ :=
  |kappa| + 3 / Real.log 2 + 2 * Real.log (N + 1 : ℕ)

theorem liuPanInverseLogDeterministicErrorBound_nonneg
    (kappa : ℝ) (N : ℕ) :
    0 ≤ liuPanInverseLogDeterministicErrorBound kappa N := by
  unfold liuPanInverseLogDeterministicErrorBound
  positivity

/-- Product-cube support turns the deterministic source sum into
`N^(2/3)` times one logarithmic error factor. -/
theorem abs_liuPanAggregateInverseLogDeterministicTerm_source_le
    (kappa : ℝ) (N y q : ℕ) (hN : 1 ≤ N) :
    |liuPanAggregateInverseLogDeterministicTerm kappa y N q
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
      3 * (N : ℝ) ^ (2 / 3 : ℝ) *
        liuPanInverseLogDeterministicErrorBound kappa N := by
  have hE := liuPanInverseLogDeterministicErrorBound_nonneg kappa N
  calc
    |liuPanAggregateInverseLogDeterministicTerm kappa y N q
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
        ∑ a ∈ Icc 1 N,
          |if a.Coprime q then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              (liuPanDiscreteInverseLogMain (y / a) -
                liuLogarithmicIntegral kappa ((y : ℝ) / a))
          else 0| := by
      unfold liuPanAggregateInverseLogDeterministicTerm
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 N,
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            liuPanInverseLogDeterministicErrorBound kappa N := by
      apply sum_le_sum
      intro a ha
      split_ifs
      · rw [abs_mul, abs_of_nonneg (liuWeight_nonneg _ _ _ _)]
        apply mul_le_mul_of_nonneg_left _ (liuWeight_nonneg _ _ _ _)
        apply
          (abs_liuPanDiscreteInverseLogMain_div_sub_liuLogarithmicIntegral_le
            kappa y a).trans
        unfold liuPanInverseLogDeterministicErrorBound
        have haN := (mem_Icc.mp ha).2
        have ha1pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
        have haNcast : ((a + 1 : ℕ) : ℝ) ≤ (N + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ haN
        linarith [Real.log_le_log ha1pos haNcast]
      · rw [abs_zero]
        exact mul_nonneg (liuWeight_nonneg _ _ _ _) hE
    _ = liuPanInverseLogDeterministicErrorBound kappa N *
          ∑ a ∈ Icc 1 N,
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      ring
    _ ≤ liuPanInverseLogDeterministicErrorBound kappa N *
          (3 * (N : ℝ) ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
          (liuSourceZ10 N) (liuSourceY3 N) hN) hE
    _ = 3 * (N : ℝ) ^ (2 / 3 : ℝ) *
          liuPanInverseLogDeterministicErrorBound kappa N := by ring

/-- The bound is independent of both maximized variables. -/
theorem liuPanAggregateInverseLogDeterministicMaxY_source_le
    (kappa : ℝ) (N q : ℕ) (hN : 1 ≤ N) :
    liuPanAggregateInverseLogDeterministicMaxY kappa N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      3 * (N : ℝ) ^ (2 / 3 : ℝ) *
        liuPanInverseLogDeterministicErrorBound kappa N := by
  unfold liuPanAggregateInverseLogDeterministicMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  unfold liuPanAggregateInverseLogDeterministicMaxL
  split_ifs
  · exact abs_liuPanAggregateInverseLogDeterministicTerm_source_le
      kappa N y q hN
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (liuPanInverseLogDeterministicErrorBound_nonneg kappa N)

/-- The normalized modulus mass is exactly the finite `H₃` mass. -/
theorem liuMainPanAggregateInverseLogDeterministicAverage_source_le
    (kappa : ℝ) (N : ℕ) (B : ℝ) (hN : 1 ≤ N) :
    liuMainPanAggregateInverseLogDeterministicAverage kappa N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
          liuPanInverseLogDeterministicErrorBound kappa N) *
        liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
  unfold liuMainPanAggregateInverseLogDeterministicAverage
  calc
    _ ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          ((3 * (N : ℝ) ^ (2 / 3 : ℝ) *
            liuPanInverseLogDeterministicErrorBound kappa N) /
              Nat.totient q) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact div_le_div_of_nonneg_right
          (liuPanAggregateInverseLogDeterministicMaxY_source_le kappa N q hN)
          (Nat.cast_nonneg _)
      · exact liuPanPrimePowerModulusWeight_nonneg q
    _ = (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
          liuPanInverseLogDeterministicErrorBound kappa N) *
        liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
      unfold liuPanPrimePowerH3Mass liuPanPrimePowerModulusWeight
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring

/-- Uniformly in the Pan parameter `B ≥ 0`, the deterministic average has the
sublinear scale `N^(2/3) log(N)^7`. -/
theorem liuMainPanAggregateInverseLogDeterministicAverage_source_le_rpow_polylog
    (kappa : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 3 ≤ N → 0 ≤ B →
      liuMainPanAggregateInverseLogDeterministicAverage kappa N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (7 : ℝ) := by
  obtain ⟨C₃, hC₃, hH₃⟩ := liuPanPrimePowerH3Mass_le_polylog
  let K : ℝ := |kappa| + 3 / Real.log 2 + 4
  let C : ℝ := 192 * K * C₃
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨C, by positivity, ?_⟩
  intro N B hN hB
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * Real.log N := by
    have hmul : N + 1 ≤ N * N := by nlinarith
    calc
      Real.log (N + 1 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hmul)
      _ = 2 * Real.log N := by
        rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
        ring
  have hE :
      liuPanInverseLogDeterministicErrorBound kappa N ≤ K * Real.log N := by
    unfold liuPanInverseLogDeterministicErrorBound
    dsimp [K]
    have hc : 0 ≤ |kappa| + 3 / Real.log (2 : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hL hc]
  have hH :
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
        (64 * C₃) * Real.log N ^ (6 : ℝ) := by
    calc
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
          C₃ * Real.log (panModulusCutoff N B + 2 : ℕ) ^ (6 : ℝ) :=
        by simpa only [Nat.cast_add, Nat.cast_ofNat] using
          hH₃ (panModulusCutoff N B)
      _ ≤ C₃ * (2 * Real.log N) ^ (6 : ℝ) := by
        have hlogQ0 :
            0 ≤ Real.log (panModulusCutoff N B + 2 : ℕ) :=
          Real.log_nonneg (by
            exact_mod_cast
              (show 1 ≤ panModulusCutoff N B + 2 by omega))
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hlogQ0
            (liuPanPrimePower_cutoff_log_add_two_le_two_mul_log N B hN hB)
            (by norm_num)) hC₃.le
      _ = (64 * C₃) * Real.log N ^ (6 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  calc
    liuMainPanAggregateInverseLogDeterministicAverage kappa N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
          liuPanInverseLogDeterministicErrorBound kappa N) *
            liuPanPrimePowerH3Mass (panModulusCutoff N B) :=
      liuMainPanAggregateInverseLogDeterministicAverage_source_le
        kappa N B hN1
    _ ≤ (3 * (N : ℝ) ^ (2 / 3 : ℝ) * (K * Real.log N)) *
          ((64 * C₃) * Real.log N ^ (6 : ℝ)) := by
      apply le_trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE (by positivity))
          (liuPanPrimePowerH3Mass_nonneg _))
      exact mul_le_mul_of_nonneg_left hH (by positivity)
    _ = C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (7 : ℝ) := by
      rw [show (7 : ℝ) = 1 + 6 by norm_num, Real.rpow_add hlogpos,
        Real.rpow_one]
      dsimp [C]
      ring

/-- Every fixed logarithmic saving eventually dominates the deterministic
`N^(2/3) log(N)^7` scale, uniformly for all `B ≥ 0`. -/
theorem eventually_liuMainPanAggregateInverseLogDeterministicBoundAt_source
    (kappa A : ℝ) (_hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ B : ℝ, 0 ≤ B →
        LiuMainPanAggregateInverseLogDeterministicBoundAt kappa N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C := by
  obtain ⟨C, hC, hpoly⟩ :=
    liuMainPanAggregateInverseLogDeterministicAverage_source_le_rpow_polylog kappa
  have hreal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (A + 7) ≤ x ^ (1 / 3 : ℝ) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop (A + 7)
      (by norm_num : (0 : ℝ) < 1 / 3)).bound (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _),
      one_mul] at hx
    exact hx
  have hnat : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (A + 7) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  rcases eventually_atTop.mp hnat with ⟨N0, hN0⟩
  refine ⟨C, hC, max N0 3, ?_⟩
  intro N hN B hB
  have hN0' : N0 ≤ N := (le_max_left N0 3).trans hN
  have hN3 : 3 ≤ N := (le_max_right N0 3).trans hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale :
      (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (7 : ℝ) ≤
        (N : ℝ) / Real.log N ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A)]
    calc
      ((N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (7 : ℝ)) *
          Real.log N ^ A =
          (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (A + 7) := by
        rw [Real.rpow_add hlogpos]
        ring
      _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left (hN0 N hN0')
          (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  unfold LiuMainPanAggregateInverseLogDeterministicBoundAt
  calc
    liuMainPanAggregateInverseLogDeterministicAverage kappa N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (7 : ℝ) :=
      hpoly N B hN3 hB
    _ = C * ((N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (7 : ℝ)) := by ring
    _ ≤ C * ((N : ℝ) / Real.log N ^ A) :=
      mul_le_mul_of_nonneg_left hscale hC.le
    _ = C * N / Real.log N ^ A := by ring

/-- The only remaining source-family hypothesis is the aggregate psi estimate. -/
def LiuMainPanAggregateInverseLogPsiSourceFamilyBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ Cpsi : ℝ, 0 < Cpsi ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        LiuMainPanAggregateInverseLogPsiBoundAt N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cpsi

/-- The unconditional deterministic estimate packages any aggregate psi
source-family bound into the corrected two-component contract. -/
theorem LiuMainPanAggregateInverseLogPsiSourceFamilyBound.to_sourceFamilyBound
    {kappa : ℝ} (hpsi : LiuMainPanAggregateInverseLogPsiSourceFamilyBound) :
    LiuMainPanAggregateInverseLogSourceFamilyBound kappa := by
  intro A hA
  rcases hpsi A hA with ⟨Cpsi, hCpsi, B, hB, Npsi, hpsiN⟩
  rcases eventually_liuMainPanAggregateInverseLogDeterministicBoundAt_source
    kappa A hA with ⟨Cdet, hCdet, Ndet, hdetN⟩
  refine ⟨Cpsi, hCpsi, Cdet, hCdet, B, hB, max Npsi Ndet, ?_⟩
  intro N hN
  exact ⟨hpsiN N ((le_max_left _ _).trans hN),
    hdetN N ((le_max_right _ _).trans hN) B hB⟩

end MathlibNt.SieveTheory.LiuWeight
