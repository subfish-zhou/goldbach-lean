import AnalyticNumberTheory.Mertens.Basic
import AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# Abel summation for prime reciprocal sums

This finite identity is the bridge from effective Chebyshev-theta estimates to
Mertens' second theorem.  It deliberately contains no asymptotic claim.
-/

namespace AnalyticNumberTheory.Mertens

open Asymptotics Filter Finset MeasureTheory Real
open scoped Chebyshev

/-- The theta-error contribution to the positive-kernel Abel formula. -/
noncomputable def thetaErrorKernel (t : ℝ) : ℝ :=
  (Chebyshev.theta t - t) * (log t + 1) / (t * log t) ^ 2

theorem thetaErrorKernel_eq (t : ℝ) :
    thetaErrorKernel t =
      Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2 -
        t * (log t + 1) / (t * log t) ^ 2 := by
  unfold thetaErrorKernel
  ring

/-- A reusable improper-integral tail estimate for the kernel that occurs in
the Mertens error term. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

/-- The Chebyshev theta function is locally integrable away from zero. -/
theorem locallyIntegrableOn_theta :
    LocallyIntegrableOn Chebyshev.theta (Set.Ici (2 : ℝ)) volume := by
  let c : ℕ → ℝ := fun p => if p.Prime then log p else 0
  have h : LocallyIntegrableOn
      (fun t : ℝ => (1 : ℝ) * ∑ p ∈ Icc 0 ⌊t⌋₊, c p) (Set.Ici 2) volume := by
    exact locallyIntegrableOn_mul_sum_Icc c (by norm_num) (locallyIntegrableOn_const 1)
  have htheta : Chebyshev.theta = fun t : ℝ => ∑ p ∈ Icc 0 ⌊t⌋₊, c p := by
    ext t
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rw [htheta]
  simpa using h

/-- The theta-error kernel is locally integrable away from the logarithmic
singularity. -/
theorem locallyIntegrableOn_thetaErrorKernel :
    LocallyIntegrableOn thetaErrorKernel (Set.Ici 2) volume := by
  have herror : LocallyIntegrableOn (fun t : ℝ => Chebyshev.theta t - t)
      (Set.Ici 2) volume :=
    locallyIntegrableOn_theta.sub
      (ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ici)
  have hcont : ContinuousOn (fun t : ℝ => (log t + 1) / (t * log t) ^ 2) (Set.Ici 2) := by
    have hlog : ContinuousOn log (Set.Ici 2) := fun t ht => by
      change 2 ≤ t at ht
      exact (Real.continuousAt_log (by linarith)).continuousWithinAt
    refine (hlog.add continuousOn_const).div
      (((continuousOn_id' _).mul hlog).pow 2) fun t ht => ?_
    change 2 ≤ t at ht
    exact pow_ne_zero 2 <| mul_ne_zero (by linarith)
      (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))
  unfold thetaErrorKernel
  simpa [mul_div_assoc, mul_comm, mul_left_comm] using
    herror.continuousOn_mul hcont isLocallyClosed_Ici

/-- The theta-error kernel has the integrable decay required for the Mertens
tail estimate. -/
theorem thetaErrorKernel_isBigO :
    thetaErrorKernel =O[atTop] fun t : ℝ => t⁻¹ / (log t) ^ 2 := by
  obtain ⟨K, hK, htheta⟩ := Asymptotics.isBigO_iff'.mp
    AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_error
  refine Asymptotics.isBigO_iff'.mpr ⟨2 * K, mul_pos (by norm_num) hK, ?_⟩
  filter_upwards [htheta, eventually_ge_atTop (exp 1)] with t hE ht
  have ht0 : 0 < t := lt_of_lt_of_le (exp_pos 1) ht
  have hlog1 : 1 ≤ log t := (Real.le_log_iff_exp_le ht0).mpr ht
  have hlog0 : 0 < log t := lt_of_lt_of_le zero_lt_one hlog1
  have hplus : log t + 1 ≤ 2 * log t := by linarith
  have hEabs : |Chebyshev.theta t - t| ≤ K * (t / log t) := by
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
      abs_of_pos (div_pos ht0 hlog0)] using hE
  have hfactor : (log t + 1) / (t * log t) ^ 2 ≤ 2 / (t ^ 2 * log t) := by
    field_simp [ne_of_gt ht0, ne_of_gt hlog0]
    linarith [hplus]
  have hfactor0 : 0 ≤ (log t + 1) / (t * log t) ^ 2 := by positivity
  rw [show ‖thetaErrorKernel t‖ = |Chebyshev.theta t - t| *
      ((log t + 1) / (t * log t) ^ 2) by
        unfold thetaErrorKernel
        calc
          |(Chebyshev.theta t - t) * (log t + 1) / (t * log t) ^ 2| =
              |Chebyshev.theta t - t| * |log t + 1| / |(t * log t) ^ 2| := by
                rw [abs_div, abs_mul]
          _ = |Chebyshev.theta t - t| * ((log t + 1) / (t * log t) ^ 2) := by
                rw [abs_of_nonneg (by linarith : 0 ≤ log t + 1),
                  abs_of_nonneg (sq_nonneg (t * log t))]
                ring]
  calc
    |Chebyshev.theta t - t| * ((log t + 1) / (t * log t) ^ 2) ≤
        (K * (t / log t)) * ((log t + 1) / (t * log t) ^ 2) :=
      mul_le_mul_of_nonneg_right hEabs hfactor0
    _ ≤ (K * (t / log t)) * (2 / (t ^ 2 * log t)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (2 * K) * ‖t⁻¹ / (log t) ^ 2‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < t⁻¹ / (log t) ^ 2)]
      have htne : t ≠ 0 := ne_of_gt ht0
      have hlogne : log t ≠ 0 := ne_of_gt hlog0
      field_simp [htne, hlogne]

/-- The theta-error kernel is integrable on the improper tail. -/
theorem integrableOn_thetaErrorKernel :
    IntegrableOn thetaErrorKernel (Set.Ioi 2) volume := by
  let g : ℝ → ℝ := fun t => t⁻¹ / (log t) ^ 2
  have hgIoi : IntegrableOn g (Set.Ioi 2) volume := by
    have htwo : (1 : ℝ) < 2 := by norm_num
    simpa only [g] using integrableOn_inv_div_log_sq_Ioi htwo
  have hgTop : IntegrableAtFilter g atTop volume :=
    ⟨Set.Ioi 2, Ioi_mem_atTop 2, hgIoi⟩
  have hO : thetaErrorKernel =O[atTop] g := by
    simpa [g] using thetaErrorKernel_isBigO
  exact (locallyIntegrableOn_thetaErrorKernel.integrableOn_of_isBigO_atTop hO hgTop).mono_set
    Set.Ioi_subset_Ici_self

/-- The constant in the Mertens reciprocal-prime asymptotic, expressed through
the theta-error kernel. -/
noncomputable def mertensSecondConstant : ℝ :=
  -log (log 2) + 1 / log 2 + ∫ t in Set.Ioi (2 : ℝ), thetaErrorKernel t

/-- The finite error integral differs from its limiting value by the negative
improper tail. -/
theorem thetaErrorKernel_interval_sub_total_eq_neg_tail {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in 2..x, thetaErrorKernel t) -
        ∫ t in Set.Ioi (2 : ℝ), thetaErrorKernel t =
      -∫ t in Set.Ioi x, thetaErrorKernel t := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi integrableOn_thetaErrorKernel hx
  linarith

/-- The theta-error kernel is integrable on every finite interval beginning at
two. -/
theorem intervalIntegrable_thetaErrorKernel {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable thetaErrorKernel volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact locallyIntegrableOn_thetaErrorKernel.integrableOn_compact_subset
    Set.Icc_subset_Ici_self isCompact_Icc

/-- Splitting the theta term in the Abel integral into its identity main term
and its theta-error term. -/
theorem theta_weighted_integral_decomposition {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in 2..x, Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2) =
      (∫ t in 2..x, t * (log t + 1) / (t * log t) ^ 2) +
        ∫ t in 2..x, thetaErrorKernel t := by
  let q : ℝ → ℝ := fun t => (log t + 1) / (t * log t) ^ 2
  have hq : ContinuousOn q (Set.Ici 2) := by
    have hlog : ContinuousOn log (Set.Ici 2) := fun t ht => by
      change 2 ≤ t at ht
      exact (Real.continuousAt_log (by linarith)).continuousWithinAt
    refine (hlog.add continuousOn_const).div
      (((continuousOn_id' _).mul hlog).pow 2) fun t ht => ?_
    change 2 ≤ t at ht
    exact pow_ne_zero 2 <| mul_ne_zero (by linarith)
      (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))
  have htheta_local : LocallyIntegrableOn (fun t : ℝ => q t * Chebyshev.theta t)
      (Set.Ici 2) volume :=
    locallyIntegrableOn_theta.continuousOn_mul hq isLocallyClosed_Ici
  have hmain_local : LocallyIntegrableOn (fun t : ℝ => t * q t) (Set.Ici 2) volume :=
    ((continuousOn_id' _).mul hq).locallyIntegrableOn measurableSet_Ici
  have htheta_int : IntervalIntegrable (fun t : ℝ => q t * Chebyshev.theta t) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact htheta_local.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc
  have hmain_int : IntervalIntegrable (fun t : ℝ => t * q t) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact hmain_local.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc
  calc
    (∫ t in 2..x, Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2) =
        ∫ t in 2..x, q t * Chebyshev.theta t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [q]
      ring
    _ = (∫ t in 2..x, t * q t) + ∫ t in 2..x, (q t * Chebyshev.theta t - t * q t) := by
      rw [intervalIntegral.integral_sub htheta_int hmain_int]
      ring
    _ = (∫ t in 2..x, t * (log t + 1) / (t * log t) ^ 2) +
        ∫ t in 2..x, thetaErrorKernel t := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro t _
        dsimp [q]
        ring
      · apply intervalIntegral.integral_congr
        intro t _
        dsimp [q]
        rw [mul_comm ((log t + 1) / (t * log t) ^ 2) (Chebyshev.theta t)]
        calc
          Chebyshev.theta t * ((log t + 1) / (t * log t) ^ 2) -
              t * ((log t + 1) / (t * log t) ^ 2) =
            Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2 -
              t * (log t + 1) / (t * log t) ^ 2 := by ring
          _ = thetaErrorKernel t := (thetaErrorKernel_eq t).symm

/-- The improper theta-error tail has the Mertens `O(1 / log x)` rate. -/
theorem thetaErrorKernel_tail_eventually :
    ∃ C > 0, ∀ᶠ x : ℝ in atTop,
      ‖∫ t in Set.Ioi x, thetaErrorKernel t‖ ≤ C / log x := by
  obtain ⟨C, hC, hO⟩ := Asymptotics.isBigO_iff'.mp thetaErrorKernel_isBigO
  obtain ⟨A, hA⟩ := eventually_atTop.mp hO
  refine ⟨C, hC, eventually_atTop.mpr ⟨max 2 A, fun x hx => ?_⟩⟩
  have hx1 : 1 < x := by linarith [le_max_left 2 A]
  apply norm_integral_Ioi_le_div_log hx1
  intro t ht
  have hAt : A ≤ t := le_trans (le_max_right 2 A |>.trans hx) ht.le
  have ht1 : 1 < t := lt_of_lt_of_le hx1 ht.le
  have ht0 : 0 < t := by linarith
  have hlog : 0 < log t := Real.log_pos ht1
  have hgt : 0 < t⁻¹ / (log t) ^ 2 :=
    div_pos (inv_pos.mpr ht0) (sq_pos_of_pos hlog)
  simpa only [Real.norm_eq_abs, abs_of_pos hgt] using hA t hAt


private theorem deriv_inv_mul_log {x : ℝ} (hx : 2 ≤ x) :
    deriv (fun u : ℝ => (u * log u)⁻¹) x =
      -(log x + 1) / (x * log x) ^ 2 := by
  have hx0 : x ≠ 0 := by linarith
  have hxlog : log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  change deriv (id * log)⁻¹ x = _
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv
    (mul_ne_zero hx0 hxlog) |>.deriv using 1
  simp only [Pi.mul_apply, id_eq, one_mul]
  field_simp [hx0, hxlog]

/-- Abel summation expresses the finite reciprocal-prime sum through the
Chebyshev theta function. -/
theorem primeReciprocalSum_eq_theta_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      (x * log x)⁻¹ * Chebyshev.theta x -
        ∫ t in 2..x,
          deriv (fun u : ℝ => (u * log u)⁻¹) t * Chebyshev.theta t := by
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) fun n ↦ log n
  unfold primeReciprocalSum primesUpTo
  rw [Nat.range_succ_eq_Icc_zero, sum_filter]
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (n * log n)⁻¹ * a n
  · refine sum_congr rfl fun n hn ↦ ?_
    split_ifs with hp
    · have hlog : log (n : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one
          (by exact_mod_cast hp.pos) (by exact_mod_cast hp.ne_one)
      simp [a, hp]
      field_simp
    · simp [a, hp]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun u : ℝ => (u * log u)⁻¹)
    (by simp [a]) (by simp [a]) x]
  · rw [← intervalIntegral.integral_of_le hx]
    simp only [a, Set.indicator_apply, sum_filter, Chebyshev.theta_eq_sum_Icc]
    grind
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hzlog : log z ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [hz.1]) (by linarith [hz.1])
    exact ((hasDerivAt_id z).mul (Real.hasDerivAt_log hz0)).inv (mul_ne_zero hz0 hzlog) |>.differentiableAt
  · refine ContinuousOn.integrableOn_Icc fun z hz ↦ ?_
    have hcont : ContinuousOn (fun y : ℝ => -(log y + 1) / (y * log y) ^ 2) (Set.Icc 2 x) := by
      have hlogcont : ContinuousOn log (Set.Icc 2 x) := fun y hy ↦
        (Real.continuousAt_log (by linarith [hy.1])).continuousWithinAt
      refine (hlogcont.add continuousOn_const).neg.div
        (((continuousOn_id' (Set.Icc 2 x)).mul hlogcont).pow 2) fun y hy ↦ ?_
      exact pow_ne_zero 2 <| mul_ne_zero (by linarith [hy.1])
        (Real.log_ne_zero_of_pos_of_ne_one (by linarith [hy.1]) (by linarith [hy.1]))
    exact (ContinuousOn.congr hcont fun y hy ↦ deriv_inv_mul_log hy.1) z hz

/-- The positive-kernel form of the Abel bridge. -/
theorem primeReciprocalSum_eq_theta_div_mul_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      Chebyshev.theta x / (x * log x) +
        ∫ t in 2..x, Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2 := by
  rw [primeReciprocalSum_eq_theta_abel hx]
  rw [show (x * log x)⁻¹ * Chebyshev.theta x = Chebyshev.theta x / (x * log x) by ring,
    sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : 2 ≤ t := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact h.1
    · linarith [h.2]
  change -(deriv (fun u : ℝ => (u * log u)⁻¹) t * Chebyshev.theta t) = _
  rw [deriv_inv_mul_log ht2]
  ring

/-- The contribution of replacing `theta` by the identity in the positive-kernel
Abel formula. -/
theorem theta_abel_main_term {x : ℝ} (hx : 2 ≤ x) :
    x / (x * log x) +
        ∫ t in 2..x, t * (log t + 1) / (t * log t) ^ 2 =
      log (log x) + (-log (log 2) + 1 / log 2) := by
  have hx1 : 1 < x := by linarith
  have hkernel :
      (∫ t in 2..x, t * (log t + 1) / (t * log t) ^ 2) =
        ∫ t in 2..x, (t⁻¹ / log t + t⁻¹ / log t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : 2 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact h.1
      · linarith [h.2]
    have ht0 : t ≠ 0 := by linarith
    have htlog : log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
      (by linarith) (by linarith)
    field_simp
  have hfirst : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := grind [Real.log_pos, Set.uIcc])
  have hsecond : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t ^ 2) volume 2 x := by
    have hlog : ContinuousOn log (Set.uIcc (2 : ℝ) x) := fun t ht ↦
      (Real.continuousAt_log (by
        rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2])).continuousWithinAt
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 x) :=
      (continuousOn_id' _).inv₀ fun t ht ↦ by
        rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2]
    apply ContinuousOn.intervalIntegrable
    exact hinv.div (hlog.pow 2) fun t ht ↦ pow_ne_zero 2 <|
      Real.log_ne_zero_of_pos_of_ne_one
        (by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2])
        (by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2])
  rw [hkernel, intervalIntegral.integral_add hfirst hsecond,
    integral_inv_div_log (by norm_num) hx1, integral_inv_div_log_sq (by norm_num) hx1]
  field_simp
  ring

/-- Exact real-variable decomposition underlying Mertens' second theorem. -/
theorem mertensSecond_error_decomposition {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant) =
      (Chebyshev.theta x - x) / (x * log x) -
        ∫ t in Set.Ioi x, thetaErrorKernel t := by
  have habel := primeReciprocalSum_eq_theta_div_mul_log_add_integral hx
  have hmain := theta_abel_main_term hx
  have hsplit := theta_weighted_integral_decomposition hx
  have htail := thetaErrorKernel_interval_sub_total_eq_neg_tail hx
  have hend : Chebyshev.theta x / (x * log x) - x / (x * log x) =
      (Chebyshev.theta x - x) / (x * log x) := by ring
  unfold mertensSecondConstant
  linarith

/-- Mertens' second theorem with an explicit `O(1 / log x)` error, on the
real-variable bridge used by downstream arithmetic applications. -/
theorem mertensSecond_eventually :
    ∃ C > 0, ∀ᶠ x : ℝ in atTop,
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
        C / log x := by
  obtain ⟨C₁, hC₁, hendpoint⟩ := Asymptotics.isBigO_iff'.mp
    AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_endpoint_error
  obtain ⟨C₂, hC₂, htail⟩ := thetaErrorKernel_tail_eventually
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  filter_upwards [htail, hendpoint,
    eventually_ge_atTop (max 2 (exp 1) : ℝ)] with x htailx hendpointx hx
  have hx2 : 2 ≤ x := le_trans (le_max_left 2 (exp 1)) hx
  have hxexp : exp 1 ≤ x := le_trans (le_max_right 2 (exp 1)) hx
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hxexp
  have hlog1 : 1 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hxexp
  have hlog0 : 0 < log x := lt_of_lt_of_le zero_lt_one hlog1
  rw [mertensSecond_error_decomposition hx2]
  calc
    |(Chebyshev.theta x - x) / (x * log x) -
        ∫ t in Set.Ioi x, thetaErrorKernel t| ≤
          |(Chebyshev.theta x - x) / (x * log x)| +
          |∫ t in Set.Ioi x, thetaErrorKernel t| := by
            simpa [sub_eq_add_neg] using abs_add_le
              ((Chebyshev.theta x - x) / (x * log x))
              (-(∫ t in Set.Ioi x, thetaErrorKernel t))
    _ ≤ C₁ / (log x) ^ 2 + C₂ / log x := by
      have hsum := add_le_add hendpointx htailx
      calc
        |(Chebyshev.theta x - x) / (x * log x)| +
            |∫ t in Set.Ioi x, thetaErrorKernel t| ≤
            C₁ * (1 / (log x) ^ 2) + C₂ / log x := by
              simpa only [Real.norm_eq_abs,
                abs_of_pos (by positivity : 0 < 1 / (log x) ^ 2)] using hsum
        _ = C₁ / (log x) ^ 2 + C₂ / log x := by ring
    _ ≤ (C₁ + C₂) / log x := by
      have hsq : log x ≤ (log x) ^ 2 := by nlinarith
      have hfirst : C₁ / (log x) ^ 2 ≤ C₁ / log x := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le hlog0 hsq) hC₁.le
      calc
        C₁ / (log x) ^ 2 + C₂ / log x ≤ C₁ / log x + C₂ / log x :=
          add_le_add hfirst le_rfl
        _ = (C₁ + C₂) / log x := by ring

/-- Natural-number Big-O interface for Mertens' second theorem. -/
theorem mertensSecond_isBigO :
    (fun n : ℕ => primeReciprocalSum n -
      (log (log (n : ℝ)) + mertensSecondConstant)) =O[atTop]
      fun n => 1 / log (n : ℝ) := by
  obtain ⟨D, _hD, hD_bound⟩ := mertensSecond_eventually
  have hreal :
      (fun x : ℝ => primeReciprocalSum ⌊x⌋₊ -
        (log (log x) + mertensSecondConstant)) =O[atTop]
        fun x : ℝ => 1 / log x := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hD_bound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 < log x := Real.log_pos hx1
    simpa [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlog),
      div_eq_mul_inv, abs_of_pos hlog] using hx
  simpa [Nat.floor_natCast] using hreal.natCast_atTop

/-- Natural-number form of Mertens' second theorem, with the finite initial
range absorbed into the uniform constant. -/
theorem mertensSecond_nat :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + mertensSecondConstant)| ≤
        C / log n := by
  obtain ⟨C, hC, hbound⟩ :=
    Asymptotics.bound_of_isBigO_nat_atTop mertensSecond_isBigO
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < log (n : ℝ) := Real.log_pos hn1
  have hne : 1 / log (n : ℝ) ≠ 0 :=
    one_div_ne_zero (ne_of_gt hlog)
  simpa [Nat.floor_natCast, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hlog), abs_of_pos hlog, div_eq_mul_inv]
    using hbound hne

/-- **Prime reciprocal sum over an interval**: for `3 ≤ a ≤ b`,
`Σ_{a ≤ p ≤ b} 1/p ≤ log(log b/log a) + E`, with an explicit
error from Mertens' second theorem. Subtracting the endpoint
`log log` terms yields the ratio `log b/log a`. -/
theorem primeReciprocalSum_range_le :
    ∃ E : ℝ, 0 < E ∧ ∀ a b : ℕ, 3 ≤ a → a ≤ b →
      primeReciprocalSum b - primeReciprocalSum (a - 1) ≤
        log (log (b : ℝ) / log (a : ℝ)) + E := by
  obtain ⟨C, hC, hM⟩ := mertensSecond_nat
  let E : ℝ := log 2 + 2 * C / log 2
  refine ⟨E, ?_, ?_⟩
  · dsimp [E]
    positivity
  · intro a b ha hb
    have hb2 : 2 ≤ b := by omega
    have ha2 : 2 ≤ a - 1 := by omega
    have hMb : primeReciprocalSum b ≤
        log (log (b : ℝ)) + mertensSecondConstant + C / log (b : ℝ) := by
      have h := hM b hb2
      have hle : primeReciprocalSum b - (log (log (b : ℝ)) + mertensSecondConstant) ≤
          C / log (b : ℝ) := (abs_le.mp h).2
      linarith
    have hMa : log (log ((a - 1 : ℕ) : ℝ)) + mertensSecondConstant -
          C / log ((a - 1 : ℕ) : ℝ) ≤ primeReciprocalSum (a - 1) := by
      have h := hM (a - 1) ha2
      have hge : -(C / log ((a - 1 : ℕ) : ℝ)) ≤
          primeReciprocalSum (a - 1) - (log (log ((a - 1 : ℕ) : ℝ)) + mertensSecondConstant) :=
        (abs_le.mp h).1
      linarith
    have hdiff : primeReciprocalSum b - primeReciprocalSum (a - 1) ≤
        log (log (b : ℝ)) - log (log ((a - 1 : ℕ) : ℝ)) +
          C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ) := by
      linarith
    have hlogb : 0 < log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
    have hloga1 : 0 < log ((a - 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < a - 1))
    have hloga : 0 < log (a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
    have hlogratio : log (log (b : ℝ)) - log (log ((a - 1 : ℕ) : ℝ)) =
        log (log (b : ℝ) / log ((a - 1 : ℕ) : ℝ)) := by
      rw [← Real.log_div (ne_of_gt hlogb) (ne_of_gt hloga1)]
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hratio_le : log (a : ℝ) / log ((a - 1 : ℕ) : ℝ) ≤ 2 := by
      have hla : log (a : ℝ) ≤ log 2 + log ((a - 1 : ℕ) : ℝ) := by
        have ha_le : (a : ℝ) ≤ 2 * ((a - 1 : ℕ) : ℝ) := by
          have : a ≤ 2 * (a - 1) := by omega
          exact_mod_cast this
        calc
          log (a : ℝ) ≤ log (2 * ((a - 1 : ℕ) : ℝ)) :=
            Real.log_le_log (by positivity) ha_le
          _ = log 2 + log ((a - 1 : ℕ) : ℝ) :=
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : ((a - 1 : ℕ) : ℝ) ≠ 0)
      have hla1ge : log 2 ≤ log ((a - 1 : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ a - 1))
      rw [div_le_iff₀ hloga1]
      nlinarith
    have hratio_ge : 1 ≤ log (a : ℝ) / log ((a - 1 : ℕ) : ℝ) := by
      have hge : log ((a - 1 : ℕ) : ℝ) ≤ log (a : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < a - 1))
          (by exact_mod_cast (by omega : a - 1 ≤ a))
      rw [le_div_iff₀ hloga1]
      simpa using hge
    have hsplit : log (log (b : ℝ) / log ((a - 1 : ℕ) : ℝ)) =
        log (log (b : ℝ) / log (a : ℝ)) + log (log (a : ℝ) / log ((a - 1 : ℕ) : ℝ)) := by
      have hprod : log (b : ℝ) / log ((a - 1 : ℕ) : ℝ) =
          log (b : ℝ) / log (a : ℝ) * (log (a : ℝ) / log ((a - 1 : ℕ) : ℝ)) := by
        field_simp [hloga.ne', hloga1.ne']
      rw [hprod]
      exact Real.log_mul (div_ne_zero (ne_of_gt hlogb) (ne_of_gt hloga))
        (div_ne_zero (ne_of_gt hloga) (ne_of_gt hloga1))
    have hratio_log : log (log (a : ℝ) / log ((a - 1 : ℕ) : ℝ)) ≤ log 2 :=
      Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hratio_ge) hratio_le
    have htail : C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ) ≤ 2 * C / log 2 := by
      have hb1 : log 2 ≤ log (b : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ b))
      have ha1 : log 2 ≤ log ((a - 1 : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ a - 1))
      have hb_inv : 1 / log (b : ℝ) ≤ 1 / log 2 := one_div_le_one_div_of_le hlog2 hb1
      have ha_inv : 1 / log ((a - 1 : ℕ) : ℝ) ≤ 1 / log 2 :=
        one_div_le_one_div_of_le hlog2 ha1
      have hsum : 1 / log (b : ℝ) + 1 / log ((a - 1 : ℕ) : ℝ) ≤ 2 / log 2 := by
        calc
          1 / log (b : ℝ) + 1 / log ((a - 1 : ℕ) : ℝ)
              ≤ 1 / log 2 + 1 / log 2 := add_le_add hb_inv ha_inv
          _ = 2 / log 2 := by ring
      calc
        C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ)
            = C * (1 / log (b : ℝ) + 1 / log ((a - 1 : ℕ) : ℝ)) := by ring
        _ ≤ C * (2 / log 2) := mul_le_mul_of_nonneg_left hsum hC.le
        _ = 2 * C / log 2 := by ring
    calc
      primeReciprocalSum b - primeReciprocalSum (a - 1)
          ≤ log (log (b : ℝ)) - log (log ((a - 1 : ℕ) : ℝ)) +
              C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ) := hdiff
      _ = log (log (b : ℝ) / log ((a - 1 : ℕ) : ℝ)) +
              C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ) := by rw [hlogratio]
      _ = log (log (b : ℝ) / log (a : ℝ)) +
              log (log (a : ℝ) / log ((a - 1 : ℕ) : ℝ)) +
              C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ) := by rw [hsplit]
      _ ≤ log (log (b : ℝ) / log (a : ℝ)) + log 2 +
              C / log (b : ℝ) + C / log ((a - 1 : ℕ) : ℝ) := by
            linarith
      _ ≤ log (log (b : ℝ) / log (a : ℝ)) + (log 2 + 2 * C / log 2) := by
            linarith
      _ = log (log (b : ℝ) / log (a : ℝ)) + E := by rfl

/-- **Interval sum as a difference**:
`Σ_{a ≤ p ≤ b} 1/p = primeReciprocalSum b - primeReciprocalSum (a-1)`. -/
theorem primeReciprocalSum_range_eq (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (Finset.range (b + 1)).filter (fun p => p.Prime ∧ a ≤ p), 1 / (p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum (a - 1) := by
  have hsmall : (Finset.range (b + 1)).filter (fun p => p.Prime ∧ p < a) =
      (Finset.range a).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hp1, hp2⟩
      exact ⟨by simpa using hp2.2, hp2.1⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hp1, hp2⟩
      have hp_lt : p < a := by simpa using hp1
      exact ⟨by simpa using (by omega : p < b + 1), ⟨hp2, hp_lt⟩⟩
  have hsplit :
      (∑ p ∈ (Finset.range (b + 1)).filter (fun p => p.Prime ∧ a ≤ p), 1 / (p : ℝ)) +
      (∑ p ∈ (Finset.range (b + 1)).filter (fun p => p.Prime ∧ p < a), 1 / (p : ℝ)) =
      (∑ p ∈ (Finset.range (b + 1)).filter Nat.Prime, 1 / (p : ℝ)) := by
    have h₁ : (∑ p ∈ (Finset.range (b + 1)).filter (fun p => p.Prime ∧ a ≤ p), 1 / (p : ℝ)) =
        (∑ p ∈ ((Finset.range (b + 1)).filter Nat.Prime).filter (fun p => a ≤ p), 1 / (p : ℝ)) := by
      congr 1
      ext p
      simp [Finset.filter_filter, and_comm, and_assoc]
    have h₂ : (∑ p ∈ (Finset.range (b + 1)).filter (fun p => p.Prime ∧ p < a), 1 / (p : ℝ)) =
        (∑ p ∈ ((Finset.range (b + 1)).filter Nat.Prime).filter (fun p => ¬ a ≤ p), 1 / (p : ℝ)) := by
      congr 1
      ext p
      simp [Finset.filter_filter, and_comm, and_assoc, not_le]
    rw [h₁, h₂]
    simpa [Finset.filter_filter, and_comm, and_assoc] using
      (Finset.sum_filter_add_sum_filter_not
        ((Finset.range (b + 1)).filter Nat.Prime) (fun p => a ≤ p) (fun p => 1 / (p : ℝ)))
  have hsmallsum : (∑ p ∈ (Finset.range (b + 1)).filter (fun p => p.Prime ∧ p < a), 1 / (p : ℝ)) =
      primeReciprocalSum (a - 1) := by
    rw [hsmall]
    unfold primeReciprocalSum primesUpTo
    congr 1
    rw [Nat.sub_add_cancel ha]
  have htotal : (∑ p ∈ (Finset.range (b + 1)).filter Nat.Prime, 1 / (p : ℝ)) =
      primeReciprocalSum b := rfl
  linarith

/-- **Double reciprocal sum factorization (Fubini)**:
`Σ_{p,q} 1/(pq) = (Σ_p 1/p)(Σ_q 1/q)`. -/
theorem primeReciprocal_doubleSum_eq (A B : Finset ℕ) :
    (∑ p ∈ A, ∑ q ∈ B, 1 / ((p : ℝ) * (q : ℝ))) =
      (∑ p ∈ A, 1 / (p : ℝ)) * (∑ q ∈ B, 1 / (q : ℝ)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- **Double reciprocal sum bound**: for `3 ≤ a ≤ b ≤ c`,
`Σ_{a ≤ p₁ ≤ b} Σ_{b ≤ p₂ ≤ c} 1/(p₁p₂)
 ≤ (log(log b/log a) + E)·(log(log c/log b) + E)`,
where `E` comes from the explicit error in Mertens' second theorem. -/
theorem primeReciprocal_doubleSum_le :
    ∃ E : ℝ, 0 < E ∧ ∀ a b c : ℕ, 3 ≤ a → a ≤ b → b ≤ c →
      (∑ p₁ ∈ (Finset.range (b + 1)).filter (fun p₁ => p₁.Prime ∧ a ≤ p₁),
        ∑ p₂ ∈ (Finset.range (c + 1)).filter (fun p₂ => p₂.Prime ∧ b ≤ p₂),
          1 / ((p₁ : ℝ) * (p₂ : ℝ))) ≤
        (log (log (b : ℝ) / log (a : ℝ)) + E) * (log (log (c : ℝ) / log (b : ℝ)) + E) := by
  obtain ⟨E, hE, hE'⟩ := primeReciprocalSum_range_le
  refine ⟨E, hE, ?_⟩
  intro a b c ha hab hbc
  have hb3 : 3 ≤ b := le_trans ha hab
  have hA : (∑ p₁ ∈ (Finset.range (b + 1)).filter (fun p₁ => p₁.Prime ∧ a ≤ p₁), 1 / (p₁ : ℝ)) ≤
      log (log (b : ℝ) / log (a : ℝ)) + E := by
    have hbnd := hE' a b ha hab
    rwa [← primeReciprocalSum_range_eq a b (by omega) hab] at hbnd
  have hB : (∑ p₂ ∈ (Finset.range (c + 1)).filter (fun p₂ => p₂.Prime ∧ b ≤ p₂), 1 / (p₂ : ℝ)) ≤
      log (log (c : ℝ) / log (b : ℝ)) + E := by
    have hbnd := hE' b c hb3 hbc
    rwa [← primeReciprocalSum_range_eq b c (by omega) hbc] at hbnd
  have hfac := primeReciprocal_doubleSum_eq
    ((Finset.range (b + 1)).filter (fun p₁ => p₁.Prime ∧ a ≤ p₁))
    ((Finset.range (c + 1)).filter (fun p₂ => p₂.Prime ∧ b ≤ p₂))
  rw [hfac]
  have hBsum0 : 0 ≤ ∑ p₂ ∈ (Finset.range (c + 1)).filter (fun p₂ => p₂.Prime ∧ b ≤ p₂), 1 / (p₂ : ℝ) := by
    exact Finset.sum_nonneg fun p _ => by positivity
  have hAlog0 : 0 ≤ log (log (b : ℝ) / log (a : ℝ)) + E := by
    have hlogb : 0 < log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
    have hloga : 0 < log (a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
    have hratio_ge : 1 ≤ log (b : ℝ) / log (a : ℝ) := by
      have hge : log (a : ℝ) ≤ log (b : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast hab)
      rw [le_div_iff₀ hloga]
      simpa using hge
    have hlog_ge : 0 ≤ log (log (b : ℝ) / log (a : ℝ)) := Real.log_nonneg hratio_ge
    linarith [hE.le]
  exact mul_le_mul hA hB hBsum0 hAlog0

end AnalyticNumberTheory.Mertens
