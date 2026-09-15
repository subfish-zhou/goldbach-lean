import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums
import AnalyticNumberTheory.Mertens.PartialSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Reciprocal-prime discrepancy on moving exponent intervals

The analytic input is the frozen real-endpoint Mertens theorem. Exact finite
prefix subtraction cancels its common constant. Both endpoints are real; the
closed lower endpoint is accounted for by a separate, decaying prime atom.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open AnalyticNumberTheory.Mertens (primeReciprocalSum primesUpTo mem_primesUpTo
  primesUpTo_mono mertensSecond_eventually mertensSecondConstant)
open scoped Classical Topology Interval

/-- The positive error constant supplied by the frozen Mertens theorem. -/
noncomputable def primeOrderedMertensConstant : ℝ :=
  mertensSecond_eventually.choose

theorem primeOrderedMertensConstant_pos : 0 < primeOrderedMertensConstant :=
  mertensSecond_eventually.choose_spec.1

/-- One real threshold, fixed before all exponent endpoints and weights. -/
noncomputable def primeOrderedMertensStart : ℝ :=
  max 2 (eventually_atTop.mp mertensSecond_eventually.choose_spec.2).choose

theorem primeOrderedMertensStart_spec :
    1 < primeOrderedMertensStart ∧
      ∀ x : ℝ, primeOrderedMertensStart ≤ x →
        |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
          primeOrderedMertensConstant / log x := by
  refine ⟨lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _), ?_⟩
  intro x hx
  exact (eventually_atTop.mp mertensSecond_eventually.choose_spec.2).choose_spec x
    ((le_max_right _ _).trans hx)

/-- Exact finite prefixes, including natural floors of real endpoints. -/
theorem primeOrdered_reciprocal_prefix_sub {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ primesIoc a b, 1 / (p : ℝ)) =
      primeReciprocalSum ⌊b⌋₊ - primeReciprocalSum ⌊a⌋₊ := by
  have he : primesIoc a b = primesUpTo ⌊b⌋₊ \ primesUpTo ⌊a⌋₊ := by
    apply Finset.ext
    intro p
    simp only [mem_primesIoc (ha.trans hab), Finset.mem_sdiff, mem_primesUpTo,
      Nat.le_floor_iff ha, Nat.le_floor_iff (ha.trans hab)]
    constructor
    · rintro ⟨hp, hpa, hpb⟩
      exact ⟨⟨hp, hpb⟩, fun h => (not_le_of_gt hpa) h.2⟩
    · rintro ⟨⟨hp, hpb⟩, hpa⟩
      exact ⟨hp, lt_of_not_ge (fun h => hpa ⟨hp, h⟩), hpb⟩
  rw [he, primeReciprocalSum, primeReciprocalSum, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff (primesUpTo_mono (Nat.floor_mono hab))

theorem primeOrdered_log_density_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * log t)) = log (log b) - log (log a) := by
  simpa only [one_div, div_eq_mul_inv, mul_inv, one_mul] using
    (integral_inv_div_log ha (ha.trans_le hab))

/-- Subtraction of the two frozen Mertens estimates, with their constant canceled. -/
theorem primeOrdered_reciprocal_discrepancy {a b : ℝ}
    (ha : primeOrderedMertensStart ≤ a) (hab : a ≤ b) :
    |(∑ p ∈ primesIoc a b, 1 / (p : ℝ)) -
      ∫ t in a..b, 1 / (t * log t)| ≤
      2 * primeOrderedMertensConstant / log a := by
  have ha1 := primeOrderedMertensStart_spec.1.trans_le ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha1
  rw [primeOrdered_reciprocal_prefix_sub ha0.le hab,
    primeOrdered_log_density_integral ha1 hab]
  have heq :
      primeReciprocalSum ⌊b⌋₊ - primeReciprocalSum ⌊a⌋₊ -
        (log (log b) - log (log a)) =
      (primeReciprocalSum ⌊b⌋₊ - (log (log b) + mertensSecondConstant)) -
        (primeReciprocalSum ⌊a⌋₊ - (log (log a) + mertensSecondConstant)) := by ring
  rw [heq]
  calc
    _ ≤ |primeReciprocalSum ⌊b⌋₊ - (log (log b) + mertensSecondConstant)| +
        |primeReciprocalSum ⌊a⌋₊ - (log (log a) + mertensSecondConstant)| :=
      abs_sub _ _
    _ ≤ primeOrderedMertensConstant / log b + primeOrderedMertensConstant / log a :=
      add_le_add (primeOrderedMertensStart_spec.2 b (ha.trans hab))
        (primeOrderedMertensStart_spec.2 a ha)
    _ ≤ primeOrderedMertensConstant / log a + primeOrderedMertensConstant / log a :=
      add_le_add (div_le_div_of_nonneg_left primeOrderedMertensConstant_pos.le
        (log_pos ha1) (log_le_log ha0 hab)) le_rfl
    _ = _ := by ring

theorem primeOrdered_exponent_density_integral {R A B : ℝ}
    (hR : 1 < R) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ t in R ^ A..R ^ B, 1 / (t * log t)) =
      ∫ t in A..B, 1 / t := by
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hlR : 0 < log R := log_pos hR
  have hB : 0 < B := hA.trans_le hAB
  rw [primeOrdered_log_density_integral (one_lt_rpow hR hA)
    (rpow_le_rpow_of_exponent_le hR.le hAB),
    log_rpow hR0, log_rpow hR0, log_mul hB.ne' hlR.ne',
    log_mul hA.ne' hlR.ne']
  rw [integral_one_div_of_pos hA hB, log_div hB.ne' hA.ne']
  ring

theorem primeOrdered_exponent_density_bounds {A B : ℝ}
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
    0 ≤ (∫ t in A..B, 1 / t) ∧ (∫ t in A..B, 1 / t) ≤ 4 := by
  have ha : 0 < A := by linarith
  have hc : ContinuousOn (fun t : ℝ => 1 / t) (uIcc A B) :=
    continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (ha.trans_le ((uIcc_of_le hAB ▸ ht).1)))
  constructor
  · apply intervalIntegral.integral_nonneg hAB
    intro t ht
    exact one_div_nonneg.mpr (ha.le.trans ht.1)
  · have h := intervalIntegral.integral_mono_on (μ := volume) hAB hc.intervalIntegrable
      (intervalIntegrable_const (c := (10 : ℝ)))
      (fun t ht => (div_le_iff₀ (ha.trans_le ht.1)).2 (by linarith [ht.1]))
    rw [intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    linarith

/-- Explicit error independent of either moving exponent endpoint. -/
noncomputable def primeOrderedDiscrepancy (R : ℝ) : ℝ :=
  20 * primeOrderedMertensConstant / log R + 1 / R ^ (1 / 10 : ℝ)

theorem primeOrderedDiscrepancy_nonneg {R : ℝ} (hR : 1 < R) :
    0 ≤ primeOrderedDiscrepancy R := by
  have := log_pos hR
  have := primeOrderedMertensConstant_pos
  unfold primeOrderedDiscrepancy
  positivity

theorem primeOrdered_reciprocal_Ioc_uniform_bound {R A B : ℝ}
    (hR : 1 < R) (hstart : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (_hB : B ≤ 1 / 2) :
    |(∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)) -
      ∫ t in A..B, 1 / t| ≤
      20 * primeOrderedMertensConstant / log R := by
  have hlR := log_pos hR
  have hlow := rpow_le_rpow_of_exponent_le hR.le hA
  have ha := hstart.trans hlow
  have hab := rpow_le_rpow_of_exponent_le hR.le hAB
  have h := primeOrdered_reciprocal_discrepancy ha hab
  rw [primeOrdered_exponent_density_integral hR (by linarith) hAB] at h
  have hlog : log (R ^ A) = A * log R := log_rpow (by linarith) A
  apply h.trans
  show 2 * primeOrderedMertensConstant / log (R ^ A) ≤
    20 * primeOrderedMertensConstant / log R
  calc
    _ ≤ 2 * primeOrderedMertensConstant / ((1 / 10) * log R) := by
      rw [hlog]
      exact div_le_div_of_nonneg_left (by positivity [primeOrderedMertensConstant_pos])
        (by positivity) (mul_le_mul_of_nonneg_right hA hlR.le)
    _ = _ := by ring

/-- Both endpoints are closed, including when the interval has zero width.
The lower prime atom costs at most `R^(-1/10)`. -/
theorem primeOrdered_reciprocal_Icc_uniform_bound {R A B : ℝ}
    (hR : 1 < R) (hstart : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
    |(∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) -
      ∫ t in A..B, 1 / t| ≤ primeOrderedDiscrepancy R := by
  rw [sum_primesIcc_eq_sum_primesIoc_add (rpow_nonneg (by linarith) _)
    (fun t : ℝ => 1 / t)]
  have h := primeOrdered_reciprocal_Ioc_uniform_bound hR hstart hA hAB hB
  have ha0 : 0 < R ^ A := rpow_pos_of_pos (by linarith) _
  have hlow : 0 < R ^ (1 / 10 : ℝ) := rpow_pos_of_pos (by linarith) _
  have hatom : |if ∃ p ∈ primesIcc (R ^ A) (R ^ B), (p : ℝ) = R ^ A
      then 1 / R ^ A else 0| ≤ 1 / R ^ (1 / 10 : ℝ) := by
    split_ifs
    · rw [abs_of_pos (one_div_pos.mpr ha0)]
      exact one_div_le_one_div_of_le hlow
        (rpow_le_rpow_of_exponent_le hR.le hA)
    · simp only [abs_zero]
      positivity
  have hh := abs_add_le
    ((∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)) - ∫ t in A..B, 1 / t)
    (if ∃ p ∈ primesIcc (R ^ A) (R ^ B), (p : ℝ) = R ^ A then 1 / R ^ A else 0)
  rw [show (∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)) +
      (if ∃ p ∈ primesIcc (R ^ A) (R ^ B), (p : ℝ) = R ^ A then 1 / R ^ A else 0) -
      (∫ t in A..B, 1 / t) =
      ((∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)) - ∫ t in A..B, 1 / t) +
      (if ∃ p ∈ primesIcc (R ^ A) (R ^ B), (p : ℝ) = R ^ A then 1 / R ^ A else 0)
      by ring]
  unfold primeOrderedDiscrepancy
  linarith

theorem primeOrderedDiscrepancy_tendsto :
    Tendsto primeOrderedDiscrepancy atTop (𝓝 0) := by
  have hl : Tendsto (fun R : ℝ => 20 * primeOrderedMertensConstant / log R)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have ha : Tendsto (fun R : ℝ => 1 / R ^ (1 / 10 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
  change Tendsto (fun R : ℝ => 20 * primeOrderedMertensConstant / log R +
    1 / R ^ (1 / 10 : ℝ)) atTop (𝓝 0)
  simpa only [add_zero] using hl.add ha

/-- The threshold precedes both endpoints, which may move or coincide. -/
theorem primeOrdered_reciprocal_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ A B : ℝ,
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |(∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) -
        ∫ t in A..B, 1 / t| < ε := by
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds hε)] with R hR hs he
  intro A B hA hAB hB
  exact (primeOrdered_reciprocal_Icc_uniform_bound hR hs hA hAB hB).trans_lt he

end Wu2008DoubleSieve
