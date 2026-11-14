module

public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Tactic.IntervalCases
public import AnalyticNumberTheory.Mertens.Theorems
public import MathlibNt.SieveTheory.Arithmetic.SingularSeries

/-!
# MathlibNt.SieveTheory.MertensTheorem

## Mertens' theorems

Mertens' theorems provide the basis for estimates of the sieve product V(z)
and its relation to the singular series 𝔖(N) in Chen's theorem.

**Mertens' second theorem**: there is a constant B₁ such that
  Σ_{p ≤ x} 1/p = log log x + B₁ + O(1/log x).

**Mertens' product formula**:
  Π_{p ≤ x} (1 - 1/p) ~ e^(-γ) / log x,
where γ is the Euler-Mascheroni constant.

Applications to Chen's theorem:
  - V(z) = Π_{p < z, p ∤ N} (1 - ν(p)/p) ≈ 𝔖(N) · e^(-γ) / log z
    in the classical notation for the sieve density;
  - the convergent product Π_{p > 2} (1 - 1/(p-1)²), the twin-prime constant,
    controls the odd-prime factors not dividing N. This does not give an
    absolute upper bound on 𝔖(N) uniform in N.

The exact finite identity below uses `singularSeriesTruncated N (z - 1)`;
both its main term and its error term retain this factor.

References:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), arXiv:2203.07871, Lemma 1
  - Nathanson, "Additive Number Theory", GTM 164
-/

@[expose] public section

namespace MathlibNt.SieveTheory.MertensTheorem

open Asymptotics Filter Real Finset
open scoped Topology

/-! ## 1. Mertens' second theorem -/

/-- The sum of prime reciprocals: Σ_{p ≤ x} 1/p. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  AnalyticNumberTheory.Mertens.primeReciprocalSum x

/-- The Chen-local reciprocal sum is definitionally the reusable ANT object. -/
theorem primeReciprocalSum_eq_analyticNumberTheory (x : ℕ) :
    primeReciprocalSum x = AnalyticNumberTheory.Mertens.primeReciprocalSum x := rfl

/-- **Mertens' second theorem**: there is a constant B₁ such that
  Σ_{p ≤ x} 1/p = log log x + B₁ + O(1/log x)

This underlies Lemma 1 in the proof of Chen's theorem.
One possible proof uses the prime number theorem and Abel summation,
but the PNT is not necessary: Mertens' theorem also has elementary proofs. -/
theorem mertens_second_theorem :
    ∃ B₁ : ℝ, ∃ C : ℝ,
      ∀ x : ℕ, 2 ≤ x →
        |primeReciprocalSum x - (log (log x) + B₁)| ≤ C / log x := by
  obtain ⟨C, hC, hbound⟩ :=
    AnalyticNumberTheory.Mertens.mertensSecond_nat
  refine ⟨AnalyticNumberTheory.Mertens.mertensSecondConstant, C, ?_⟩
  intro x hx
  simpa only [primeReciprocalSum_eq_analyticNumberTheory] using hbound x hx

/-! ### Smooth weights on logarithmic prime intervals -/

/-- The floor of the real power used as an exact natural cutoff. -/
noncomputable def rpowFloor (N : ℕ) (a : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ a)

/-- The reciprocal-prime sum with a test function on logarithmic scale.

The `Ioc` endpoints are literal floors of the real powers.  Thus, when `N ≥ 1`,
membership is exactly `N ^ a < p ∧ p ≤ N ^ b`; no endpoint error is hidden in
the definition. -/
noncomputable def weightedPrimeReciprocalLogSum
    (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc (rpowFloor N a) (rpowFloor N b)).filter Nat.Prime,
    f (log p / log N) / p

/-- The floor cutoffs encode the intended half-open real-power interval
exactly. -/
theorem mem_Ioc_rpowFloor_iff {N p : ℕ} {a b : ℝ} :
    p ∈ Finset.Ioc (rpowFloor N a) (rpowFloor N b) ↔
      (N : ℝ) ^ a < p ∧ (p : ℝ) ≤ (N : ℝ) ^ b := by
  have ha : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hb : 0 ≤ (N : ℝ) ^ b := Real.rpow_nonneg (Nat.cast_nonneg N) _
  simp only [Finset.mem_Ioc, rpowFloor]
  rw [Nat.floor_lt ha, Nat.le_floor_iff hb]

/-- The arithmetic coefficient whose prefix sum is Mertens'
`primeReciprocalSum`. -/
private noncomputable def primeReciprocalCoeff (p : ℕ) : ℝ :=
  if p.Prime then 1 / (p : ℝ) else 0

private theorem sum_primeReciprocalCoeff_Icc (n : ℕ) :
    ∑ p ∈ Finset.Icc 0 n, primeReciprocalCoeff p = primeReciprocalSum n := by
  unfold primeReciprocalCoeff
  change _ = ∑ p ∈ n.primesLE, 1 / (p : ℝ)
  rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]

/-- Derivative of a test function pulled back to logarithmic scale. -/
noncomputable def logScaleDeriv (f' : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  f' (log t / log N) / (t * log N)

private theorem hasDerivAt_logScale
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {N : ℕ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => f (log u / log N))
      (logScaleDeriv f' N t) t := by
  have h := (hf (log t / log N)).comp t
    ((Real.hasDerivAt_log ht.ne').div_const (log N))
  have heq : logScaleDeriv f' N t =
      f' (log t / log N) * (t⁻¹ / log N) := by
    change f' (log t / log N) / (t * log N) = _
    ring
  rw [heq]
  simpa only [Function.comp_def] using h

/-- Finite Abel summation for a logarithmically rescaled smooth test function.
This is an exact identity, including both floored real-power endpoints. -/
theorem weightedPrimeReciprocalLogSum_eq_sub_sub_integral
    {a b : ℝ} (_ha : 0 < a) (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {N : ℕ} (hN : 1 < N) :
    weightedPrimeReciprocalLogSum f N a b =
      f b * primeReciprocalSum (rpowFloor N b) -
      f a * primeReciprocalSum (rpowFloor N a) -
      ∫ t in Set.Ioc ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        logScaleDeriv f' N t * primeReciprocalSum (Nat.floor t) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNa : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos (by positivity) _
  have hpows : (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hNr) hab
  have hdiff : ∀ t ∈ Set.Icc ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      DifferentiableAt ℝ (fun u : ℝ => f (log u / log N)) t := by
    intro t ht
    exact (hasDerivAt_logScale hf (lt_of_lt_of_le hNa ht.1)).differentiableAt
  have hcont : ContinuousOn (logScaleDeriv f' N)
      (Set.Icc ((N : ℝ) ^ a) ((N : ℝ) ^ b)) := by
    have hlogN : 0 < log (N : ℝ) := Real.log_pos hNr
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hNa ht.1
    apply ContinuousAt.continuousWithinAt
    exact
      (hf'.continuousAt.comp
        ((Real.continuousAt_log htpos.ne').div_const _)).div
        (continuousAt_id.mul continuousAt_const)
        (mul_ne_zero htpos.ne' hlogN.ne')
  have hderiv : ∀ t ∈ Set.Icc ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      deriv (fun u : ℝ => f (log u / log N)) t = logScaleDeriv f' N t := by
    intro t ht
    exact (hasDerivAt_logScale hf (lt_of_lt_of_le hNa ht.1)).deriv
  have hAbel := sum_mul_eq_sub_sub_integral_mul
    primeReciprocalCoeff (le_of_lt hNa) hpows hdiff
    (hcont.integrableOn_Icc.congr_fun
      (fun t ht => (hderiv t ht).symm) measurableSet_Icc)
  rw [show Nat.floor ((N : ℝ) ^ a) = rpowFloor N a by rfl,
    show Nat.floor ((N : ℝ) ^ b) = rpowFloor N b by rfl] at hAbel
  simp only [sum_primeReciprocalCoeff_Icc] at hAbel
  have hlogN : log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNr)
  have hscale (x : ℝ) : log ((N : ℝ) ^ x) / log N = x := by
    rw [Real.log_rpow (by positivity)]
    exact mul_div_cancel_right₀ x hlogN
  have hint :
      (∫ t in Set.Ioc ((N : ℝ) ^ a) ((N : ℝ) ^ b),
          deriv (fun u : ℝ => f (log u / log N)) t *
            primeReciprocalSum (Nat.floor t)) =
        ∫ t in Set.Ioc ((N : ℝ) ^ a) ((N : ℝ) ^ b),
          logScaleDeriv f' N t * primeReciprocalSum (Nat.floor t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hderiv t ⟨le_of_lt ht.1, ht.2⟩]
  rw [hscale a, hscale b, hint] at hAbel
  rw [← hAbel]
  unfold weightedPrimeReciprocalLogSum primeReciprocalCoeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

/-- A floored positive real power tends to infinity. -/
theorem tendsto_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rpowFloor N a) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

theorem eventually_two_le_rpowFloor {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ rpowFloor N a :=
  (tendsto_rpowFloor_atTop ha).eventually (eventually_ge_atTop 2)

/-- Flooring changes a positive real power by a relative error tending to zero. -/
theorem tendsto_rpowFloor_div_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (rpowFloor N a : ℝ) / ((N : ℝ) ^ a))
      atTop (nhds 1) := by
  exact tendsto_nat_floor_div_atTop.comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

theorem tendsto_log_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => log (rpowFloor N a : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_rpowFloor_atTop ha))

theorem tendsto_log_rpowFloor_sub_log_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      log (rpowFloor N a : ℝ) - log ((N : ℝ) ^ a))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpowFloor_div_rpow ha).log one_ne_zero
  simpa only [Real.log_one] using h.congr' (by
    filter_upwards [eventually_two_le_rpowFloor ha,
      hpow.eventually (eventually_gt_atTop 0)] with N hfloor hpowPos
    rw [Real.log_div (by positivity) (ne_of_gt hpowPos)])

/-- The log--log asymptotic with the exact identity
`log (N ^ a) = a * log N`. -/
theorem tendsto_log_log_rpowFloor_sub {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      log (log (rpowFloor N a : ℝ)) -
        (log a + log (log (N : ℝ)))) atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlogpow : Tendsto (fun N : ℕ => log ((N : ℝ) ^ a))
      atTop atTop :=
    Real.tendsto_log_atTop.comp hpow
  have hsmallRatio : Tendsto (fun N : ℕ =>
      (log (rpowFloor N a : ℝ) - log ((N : ℝ) ^ a)) /
        log ((N : ℝ) ^ a)) atTop (nhds 0) :=
    (tendsto_log_rpowFloor_sub_log_rpow ha).div_atTop hlogpow
  have hden : ∀ᶠ N : ℕ in atTop, log ((N : ℝ) ^ a) ≠ 0 := by
    filter_upwards [hlogpow.eventually (eventually_gt_atTop 0)] with N hN
    exact ne_of_gt hN
  have hlogRatio : Tendsto (fun N : ℕ =>
      log (rpowFloor N a : ℝ) / log ((N : ℝ) ^ a))
      atTop (nhds 1) := by
    simpa only [zero_add] using (hsmallRatio.add_const 1).congr' (by
      filter_upwards [hden] with N hN
      field_simp [hN]
      ring)
  have hloglogRatio := hlogRatio.log one_ne_zero
  simpa only [Real.log_one] using hloglogRatio.congr' (by
    filter_upwards [eventually_two_le_rpowFloor ha,
      hlogpow.eventually (eventually_gt_atTop 0),
      eventually_gt_atTop (1 : ℕ)] with N hfloor hlogpowPos hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast Nat.zero_lt_of_lt hN
    have hlogNpos : 0 < log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hlogfloorPos : 0 < log (rpowFloor N a : ℝ) :=
      Real.log_pos (by
        exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hfloor)
    rw [Real.log_div (ne_of_gt hlogfloorPos) (ne_of_gt hlogpowPos)]
    congr 1
    rw [Real.log_rpow hNpos,
      Real.log_mul (ne_of_gt ha) (ne_of_gt hlogNpos)])

private theorem tendsto_mertens_error_rpowFloor {a B C : ℝ} (ha : 0 < a)
    (hM : ∀ x : ℕ, 2 ≤ x →
      |primeReciprocalSum x - (log (log x) + B)| ≤ C / log x) :
    Tendsto (fun N : ℕ =>
      primeReciprocalSum (rpowFloor N a) -
        (log (log (rpowFloor N a)) + B)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : Tendsto
      (fun N : ℕ => C / log (rpowFloor N a : ℝ))
      atTop (nhds 0) :=
    (tendsto_log_rpowFloor_atTop ha).const_div_atTop C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_
  filter_upwards [eventually_two_le_rpowFloor ha] with N hN
  simpa only [Real.norm_eq_abs] using hM (rpowFloor N a) hN

private theorem tendsto_mertens_prefix_normalized {a B C : ℝ} (ha : 0 < a)
    (hM : ∀ x : ℕ, 2 ≤ x →
      |primeReciprocalSum x - (log (log x) + B)| ≤ C / log x) :
    Tendsto (fun N : ℕ =>
      primeReciprocalSum (rpowFloor N a) -
        (log a + log (log (N : ℝ)) + B))
      atTop (nhds 0) := by
  have h := (tendsto_mertens_error_rpowFloor ha hM).add
    (tendsto_log_log_rpowFloor_sub ha)
  convert h using 1
  · funext N
    ring
  · ring_nf

/-- For a constant test function, the exact real-power prime interval has the
expected logarithmic limit.  This is the base case for finite-step
approximations of general continuous test functions. -/
theorem tendsto_weightedPrimeReciprocalLogSum_const
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ =>
      weightedPrimeReciprocalLogSum (fun _ => c) N a b)
      atTop (nhds (c * log (b / a))) := by
  obtain ⟨B, C, hM⟩ := mertens_second_theorem
  have hb : 0 < b := ha.trans hab
  have haLimit := tendsto_mertens_prefix_normalized ha hM
  have hbLimit := tendsto_mertens_prefix_normalized hb hM
  have hbase : Tendsto (fun N : ℕ =>
      primeReciprocalSum (rpowFloor N b) -
        primeReciprocalSum (rpowFloor N a))
      atTop (nhds (log b - log a)) := by
    have h := (hbLimit.sub haLimit).add_const (log b - log a)
    convert h using 1
    · funext N
      ring
    · ring_nf
  have hdiff := hbase.const_mul c
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  apply hdiff.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hid := weightedPrimeReciprocalLogSum_eq_sub_sub_integral
    ha (le_of_lt hab) (f := fun _ => c) (f' := fun _ => 0)
    (fun x => hasDerivAt_const x c) continuous_const hN
  simp only [zero_mul, MeasureTheory.integral_zero, sub_zero,
    logScaleDeriv, zero_div] at hid
  rw [hid]
  ring


/-- Mertens' prefix with the common, scale-dependent term removed. -/
private noncomputable def normalizedPrimeReciprocalPrefix
    (B : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  primeReciprocalSum (rpowFloor N x) - (log (log (N : ℝ)) + B)

private theorem tendsto_normalizedPrimeReciprocalPrefix
    {x B C : ℝ} (hx : 0 < x)
    (hM : ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + B)| ≤ C / log n) :
    Tendsto (fun N : ℕ => normalizedPrimeReciprocalPrefix B N x)
      atTop (nhds (log x)) := by
  have h := (tendsto_mertens_prefix_normalized hx hM).add_const (log x)
  convert h using 1
  · funext N
    unfold normalizedPrimeReciprocalPrefix
    ring
  · ring_nf

private theorem primeReciprocalSum_mono_early :
    Monotone primeReciprocalSum := by
  intro m n hmn
  rw [primeReciprocalSum_eq_analyticNumberTheory,
    primeReciprocalSum_eq_analyticNumberTheory]
  exact AnalyticNumberTheory.Mertens.primeReciprocalSum_mono hmn

private theorem normalizedPrimeReciprocalPrefix_mono
    (B : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Monotone (normalizedPrimeReciprocalPrefix B N) := by
  intro x y hxy
  apply sub_le_sub_right
  apply primeReciprocalSum_mono_early
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hxy

private theorem measurable_normalizedPrimeReciprocalPrefix
    (B : ℝ) {N : ℕ} (hN : N ≠ 0) :
    Measurable (normalizedPrimeReciprocalPrefix B N) := by
  have hpow : Measurable (fun x : ℝ => (N : ℝ) ^ x) :=
    (Real.continuous_const_rpow (by exact_mod_cast hN)).measurable
  have hfloor : Measurable (fun x : ℝ => rpowFloor N x) := by
    exact hpow.nat_floor
  have hprefix : Measurable (fun x : ℝ =>
      primeReciprocalSum (rpowFloor N x)) :=
    (measurable_of_countable primeReciprocalSum).comp hfloor
  exact hprefix.sub measurable_const

/-- The normalized Mertens prefixes may be integrated against any continuous
function on a fixed positive interval.  Endpoint monotonicity supplies the
uniform dominator, avoiding a separate uniform Mertens theorem. -/
private theorem tendsto_integral_mul_normalizedPrimeReciprocalPrefix
    {a b B C : ℝ} (ha : 0 < a) (hab : a < b)
    (hM : ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + B)| ≤ C / log n)
    (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun N : ℕ => ∫ x in a..b,
      g x * normalizedPrimeReciprocalPrefix B N x)
      atTop (nhds (∫ x in a..b, g x * log x)) := by
  let K : ℝ := |log a| + |log b| + 2
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have haLim := tendsto_normalizedPrimeReciprocalPrefix ha hM
  have hbLim := tendsto_normalizedPrimeReciprocalPrefix (ha.trans hab) hM
  have haBound : ∀ᶠ N : ℕ in atTop,
      |normalizedPrimeReciprocalPrefix B N a| ≤ K := by
    have h := (Metric.tendsto_nhds.1 haLim) 1 zero_lt_one
    filter_upwards [h] with N hN
    rw [Real.dist_eq] at hN
    calc
      |normalizedPrimeReciprocalPrefix B N a|
          = |log a + (normalizedPrimeReciprocalPrefix B N a - log a)| := by ring_nf
      _ ≤ |log a| + |normalizedPrimeReciprocalPrefix B N a - log a| :=
        by simpa only [Real.norm_eq_abs] using
          norm_add_le (log a) (normalizedPrimeReciprocalPrefix B N a - log a)
      _ ≤ K := by
        dsimp [K]
        nlinarith [abs_nonneg (log b)]
  have hbBound : ∀ᶠ N : ℕ in atTop,
      |normalizedPrimeReciprocalPrefix B N b| ≤ K := by
    have h := (Metric.tendsto_nhds.1 hbLim) 1 zero_lt_one
    filter_upwards [h] with N hN
    rw [Real.dist_eq] at hN
    calc
      |normalizedPrimeReciprocalPrefix B N b|
          = |log b + (normalizedPrimeReciprocalPrefix B N b - log b)| := by ring_nf
      _ ≤ |log b| + |normalizedPrimeReciprocalPrefix B N b - log b| :=
        by simpa only [Real.norm_eq_abs] using
          norm_add_le (log b) (normalizedPrimeReciprocalPrefix B N b - log b)
      _ ≤ K := by
        dsimp [K]
        nlinarith [abs_nonneg (log a)]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => K * |g x|) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (hg.measurable.mul
      (measurable_normalizedPrimeReciprocalPrefix B hN.ne')).aestronglyMeasurable.restrict
  · filter_upwards [haBound, hbBound, eventually_ge_atTop (1 : ℕ)] with N hNa hNb hN
    filter_upwards with x hx
    have hx' : x ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le (le_of_lt hab)] using hx
    have hmono := normalizedPrimeReciprocalPrefix_mono B hN
    have hax : normalizedPrimeReciprocalPrefix B N a ≤
        normalizedPrimeReciprocalPrefix B N x := hmono (le_of_lt hx'.1)
    have hxb : normalizedPrimeReciprocalPrefix B N x ≤
        normalizedPrimeReciprocalPrefix B N b := hmono hx'.2
    have hxabs : |normalizedPrimeReciprocalPrefix B N x| ≤ K := by
      rw [abs_le]
      constructor
      · have := (abs_le.mp hNa).1
        linarith
      · exact hxb.trans (abs_le.mp hNb).2
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |g x| * |normalizedPrimeReciprocalPrefix B N x| =
          |normalizedPrimeReciprocalPrefix B N x| * |g x| := mul_comm _ _
      _ ≤ K * |g x| := mul_le_mul_of_nonneg_right hxabs (abs_nonneg _)
  · exact (hg.abs.const_mul K).intervalIntegrable a b
  · filter_upwards with x hx
    have hx' : x ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le (le_of_lt hab)] using hx
    exact (tendsto_const_nhds.mul
      (tendsto_normalizedPrimeReciprocalPrefix (ha.trans hx'.1) hM))

/-- Change variables `t = N ^ x` in the Abel integral.  The statement uses a
set integral on the left because that is the normalization in Mathlib's Abel
summation theorem. -/
private theorem integral_logScaleDeriv_mul_primeReciprocalSum
    {a b : ℝ} (hab : a ≤ b) {f' : ℝ → ℝ} {N : ℕ} (hN : 1 < N) :
    (∫ t in Set.Ioc ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      logScaleDeriv f' N t * primeReciprocalSum (Nat.floor t)) =
      ∫ x in a..b, f' x * primeReciprocalSum (rpowFloor N x) := by
  have hNr : (0 : ℝ) < N := by positivity
  have hlogN : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hpows : (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.le_of_lt hN)) hab
  rw [← intervalIntegral.integral_of_le hpows]
  let G : ℝ → ℝ := fun t =>
    logScaleDeriv f' N t * primeReciprocalSum (Nat.floor t)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := a) (b := b) (f := fun x : ℝ => (N : ℝ) ^ x)
    (f' := fun x : ℝ => (N : ℝ) ^ x * log N) (g := G)
    (Real.continuous_const_rpow (ne_of_gt hNr)).continuousOn
    (fun x _ => (Real.hasStrictDerivAt_const_rpow hNr x).hasDerivAt)
    (fun x _ => mul_nonneg (Real.rpow_nonneg (le_of_lt hNr) _)
      (le_of_lt hlogN))
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only [G, Function.comp_apply, logScaleDeriv, rpowFloor]
  have hpow : 0 < (N : ℝ) ^ x := Real.rpow_pos_of_pos hNr _
  have hscale : log ((N : ℝ) ^ x) / log N = x := by
    rw [Real.log_rpow hNr]
    field_simp [hlogN.ne']
  rw [hscale]
  field_simp [hpow.ne', hlogN.ne']

private theorem integral_div_eq_boundary_sub_integral_mul_log
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') :
    (∫ x in a..b, f x / x) =
      f b * log b - f a * log a - ∫ x in a..b, f' x * log x := by
  have hlog : ∀ x ∈ Set.uIcc a b,
      HasDerivAt log (1 / x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    simpa only [one_div] using
      Real.hasDerivAt_log (ne_of_gt (ha.trans_le hx'.1))
  have hinv : ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (ha.trans_le hx.1))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := f) (v := log) (u' := f')
    (v' := fun x : ℝ => 1 / x)
    (fun x _ => hf x) hlog
    (hf'.intervalIntegrable a b)
    (ContinuousOn.intervalIntegrable_of_Icc hab hinv)
  simpa only [mul_one_div] using hparts

private theorem intervalIntegrable_mul_normalizedPrimeReciprocalPrefix
    {a b B : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    {N : ℕ} (hN : 1 ≤ N) :
    IntervalIntegrable
      (fun x => g x * normalizedPrimeReciprocalPrefix B N x)
      MeasureTheory.volume a b := by
  let K := max
    |normalizedPrimeReciprocalPrefix B N a|
    |normalizedPrimeReciprocalPrefix B N b|
  have hHbound : ∀ x ∈ Set.Icc a b,
      |normalizedPrimeReciprocalPrefix B N x| ≤ K := by
    intro x hx
    have hmono := normalizedPrimeReciprocalPrefix_mono B hN
    rw [abs_le]
    constructor
    · have hleft := (neg_le_of_abs_le (le_max_left
          |normalizedPrimeReciprocalPrefix B N a|
          |normalizedPrimeReciprocalPrefix B N b|))
      exact hleft.trans (hmono hx.1)
    · exact (hmono hx.2).trans
        (le_trans (le_abs_self _) (le_max_right _ _))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hgInt : MeasureTheory.IntegrableOn g (Set.Icc a b) :=
    hg.integrableOn_Icc
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (normalizedPrimeReciprocalPrefix B N)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (measurable_normalizedPrimeReciprocalPrefix B
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))).aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc a b),
      ‖normalizedPrimeReciprocalPrefix B N x‖ ≤ K := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with x hx
    simpa only [Real.norm_eq_abs] using hHbound x hx
  have hprod := hgInt.bdd_smul K hmeas hbound
  exact hprod.congr (Filter.Eventually.of_forall fun x => by
    simp only [smul_eq_mul]
    exact mul_comm _ _)

private theorem weightedPrimeReciprocalLogSum_eq_normalized
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {N : ℕ} (hN : 1 < N) :
    weightedPrimeReciprocalLogSum f N a b =
      f b * normalizedPrimeReciprocalPrefix B N b -
      f a * normalizedPrimeReciprocalPrefix B N a -
      ∫ x in a..b, f' x * normalizedPrimeReciprocalPrefix B N x := by
  let L : ℝ := log (log (N : ℝ)) + B
  have hf'Int : IntervalIntegrable f' MeasureTheory.volume a b :=
    hf'.intervalIntegrable a b
  have hHInt : IntervalIntegrable
      (fun x => f' x * normalizedPrimeReciprocalPrefix B N x)
      MeasureTheory.volume a b :=
    intervalIntegrable_mul_normalizedPrimeReciprocalPrefix
      (B := B) hab f' hf' (N := N) (le_of_lt hN)
  have hfun :
      (fun x => f' x * primeReciprocalSum (rpowFloor N x)) =
        (fun x => f' x * normalizedPrimeReciprocalPrefix B N x + L * f' x) := by
    funext x
    simp only [normalizedPrimeReciprocalPrefix, L]
    ring

  have hint :
      (∫ x in a..b, f' x * primeReciprocalSum (rpowFloor N x)) =
        (∫ x in a..b, f' x * normalizedPrimeReciprocalPrefix B N x) +
          L * ∫ x in a..b, f' x := by
    rw [hfun, intervalIntegral.integral_add hHInt (hf'Int.const_mul L),
      intervalIntegral.integral_const_mul]
  have hFTC : (∫ x in a..b, f' x) = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hf x) hf'Int
  rw [weightedPrimeReciprocalLogSum_eq_sub_sub_integral ha hab hf hf' hN,
    integral_logScaleDeriv_mul_primeReciprocalSum hab hN, hint, hFTC]
  simp only [normalizedPrimeReciprocalPrefix, L]
  ring

/-- A continuously differentiable test function on a fixed positive logarithmic
interval has the expected Mertens-weighted prime-sum limit.  The sum uses the
literal floored cutoffs `⌊N ^ a⌋` and `⌊N ^ b⌋`. -/
theorem tendsto_weightedPrimeReciprocalLogSum_of_hasDerivAt
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') :
    Tendsto (fun N : ℕ => weightedPrimeReciprocalLogSum f N a b)
      atTop (nhds (∫ x in a..b, f x / x)) := by
  obtain ⟨B, C, hM⟩ := mertens_second_theorem
  have hb : 0 < b := ha.trans hab
  have haLim := tendsto_normalizedPrimeReciprocalPrefix ha hM
  have hbLim := tendsto_normalizedPrimeReciprocalPrefix hb hM
  have hintLim :=
    tendsto_integral_mul_normalizedPrimeReciprocalPrefix
      ha hab hM f' hf'
  have hlim :
      Tendsto
        (fun N : ℕ =>
          f b * normalizedPrimeReciprocalPrefix B N b -
          f a * normalizedPrimeReciprocalPrefix B N a -
          ∫ x in a..b, f' x * normalizedPrimeReciprocalPrefix B N x)
        atTop
        (nhds
          (f b * log b - f a * log a -
            ∫ x in a..b, f' x * log x)) :=
    ((tendsto_const_nhds.mul hbLim).sub
      (tendsto_const_nhds.mul haLim)).sub hintLim
  rw [integral_div_eq_boundary_sub_integral_mul_log ha (le_of_lt hab) hf hf']
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  exact (weightedPrimeReciprocalLogSum_eq_normalized
    (B := B) ha (le_of_lt hab) hf hf' hN).symm

private theorem log_div_log_mem_Icc
    {a b : ℝ} {N p : ℕ} (hN : 1 < N)
    (hp : p ∈ Finset.Ioc (rpowFloor N a) (rpowFloor N b)) :
    log (p : ℝ) / log (N : ℝ) ∈ Set.Icc a b := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < log (N : ℝ) := Real.log_pos hNr
  have hpows := (mem_Ioc_rpowFloor_iff.mp hp)
  have hpa : 0 < (p : ℝ) :=
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < N) a).trans hpows.1
  have hloga : log ((N : ℝ) ^ a) < log (p : ℝ) :=
    Real.strictMonoOn_log
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < N) a)
      hpa hpows.1
  have hlogb : log (p : ℝ) ≤ log ((N : ℝ) ^ b) :=
    Real.strictMonoOn_log.monotoneOn hpa
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < N) b) hpows.2
  rw [Real.log_rpow (by positivity)] at hloga hlogb
  constructor
  · rw [le_div_iff₀ hlogN]
    exact le_of_lt hloga
  · rw [div_le_iff₀ hlogN]
    exact hlogb

private theorem weightedPrimeReciprocalLogSum_sub_le
    {a b ε : ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε)
    {N : ℕ} (hN : 1 < N) :
    |weightedPrimeReciprocalLogSum f N a b -
        weightedPrimeReciprocalLogSum g N a b| ≤
      ε * weightedPrimeReciprocalLogSum (fun _ => 1) N a b := by
  let s := (Finset.Ioc (rpowFloor N a) (rpowFloor N b)).filter Nat.Prime
  have hterm : ∀ p ∈ s,
      |f (log p / log N) / p - g (log p / log N) / p| ≤
        ε * (1 / (p : ℝ)) := by
    intro p hp
    have hpIoc : p ∈ Finset.Ioc (rpowFloor N a) (rpowFloor N b) :=
      (Finset.mem_filter.mp hp).1
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have happrox := hfg _ (log_div_log_mem_Icc hN hpIoc)
    rw [← sub_div, abs_div]
    simpa only [abs_of_pos hp0, div_eq_mul_inv, one_mul] using
      (div_le_div_of_nonneg_right happrox (le_of_lt hp0))
  unfold weightedPrimeReciprocalLogSum
  change |(∑ p ∈ s, f (log p / log N) / p) -
      ∑ p ∈ s, g (log p / log N) / p| ≤
    ε * ∑ p ∈ s, (1 : ℝ) / p
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ s, (f (log p / log N) / p - g (log p / log N) / p)|
        ≤ ∑ p ∈ s, |f (log p / log N) / p - g (log p / log N) / p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ s, ε * (1 / (p : ℝ)) :=
      Finset.sum_le_sum fun p hp => hterm p hp
    _ = ε * ∑ p ∈ s, (1 : ℝ) / p := by rw [Finset.mul_sum]

private theorem integral_div_sub_le
    {a b ε : ℝ} {f g : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hε : 0 ≤ ε) (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b))
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε) :
    |(∫ x in a..b, f x / x) - ∫ x in a..b, g x / x| ≤
      (ε / a) * (b - a) := by
  have hne : ∀ x ∈ Set.Icc a b, x ≠ 0 := by
    intro x hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hfInt : IntervalIntegrable (fun x => f x / x)
      MeasureTheory.volume a b :=
    (hf.div continuousOn_id hne).intervalIntegrable_of_Icc hab
  have hgInt : IntervalIntegrable (fun x => g x / x)
      MeasureTheory.volume a b :=
    (hg.div continuousOn_id hne).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_sub hfInt hgInt]
  have hbound : ∀ x ∈ Set.uIoc a b,
      ‖f x / x - g x / x‖ ≤ ε / a := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hxpos : 0 < x := ha.trans_le hx'.1
    rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hxpos]
    rw [div_le_div_iff₀ hxpos ha]
    exact mul_le_mul (hfg x hx') hx'.1 (le_of_lt ha) hε
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := ε / a)
      (f := fun x => f x / x - g x / x) hbound)

/-- A continuous test function on a fixed positive logarithmic interval has the
expected reciprocal-prime limit. -/
theorem tendsto_weightedPrimeReciprocalLogSum
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun N : ℕ => weightedPrimeReciprocalLogSum f N a b)
      atTop (nhds (∫ x in a..b, f x / x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M : ℝ := log (b / a) + 1
  let J : ℝ := (b - a) / a
  let K : ℝ := max M J
  have hratio : 1 < b / a := (one_lt_div ha).2 hab
  have hM : 0 < M := by
    dsimp [M]
    nlinarith [Real.log_pos hratio]
  have hJ : 0 < J := by
    dsimp [J]
    positivity
  have hK : 0 < K := hM.trans_le (le_max_left _ _)
  let δ : ℝ := ε / (3 * K)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn a b f hf δ hδ
  have hfp : ∀ x ∈ Set.Icc a b,
      |f x - Polynomial.eval x p| ≤ δ := by
    intro x hx
    rw [abs_sub_comm]
    exact le_of_lt (hp x hx)
  have hpLim :=
    tendsto_weightedPrimeReciprocalLogSum_of_hasDerivAt
      ha hab (fun x => p.hasDerivAt x) p.derivative.continuous
  have hpClose : ∀ᶠ N : ℕ in atTop,
      dist (weightedPrimeReciprocalLogSum (Polynomial.eval · p) N a b)
        (∫ x in a..b, Polynomial.eval x p / x) < ε / 3 :=
    (Metric.tendsto_nhds.1 hpLim) (ε / 3) (by positivity)
  have honeLim :=
    tendsto_weightedPrimeReciprocalLogSum_const
      (c := 1) ha hab
  have honeClose : ∀ᶠ N : ℕ in atTop,
      dist (weightedPrimeReciprocalLogSum (fun _ => 1) N a b)
        (log (b / a)) < 1 :=
    (Metric.tendsto_nhds.1 (by simpa using honeLim)) 1 zero_lt_one
  have hintApprox :
      |(∫ x in a..b, f x / x) -
          ∫ x in a..b, Polynomial.eval x p / x| ≤ δ * J := by
    have h := integral_div_sub_le ha (le_of_lt hab)
      (le_of_lt hδ) hf p.continuous.continuousOn hfp
    dsimp only [J]
    calc
      _ ≤ (δ / a) * (b - a) := h
      _ = δ * ((b - a) / a) := by ring
  filter_upwards [hpClose, honeClose, eventually_gt_atTop (1 : ℕ)]
    with N hpN honeN hN
  rw [Real.dist_eq] at hpN honeN ⊢
  have honeBound :
      weightedPrimeReciprocalLogSum (fun _ => 1) N a b < M := by
    rw [abs_lt] at honeN
    dsimp [M]
    linarith [honeN.2]
  have hsumApprox :
      |weightedPrimeReciprocalLogSum f N a b -
          weightedPrimeReciprocalLogSum (Polynomial.eval · p) N a b| <
        ε / 3 := by
    have h := weightedPrimeReciprocalLogSum_sub_le hfp hN
    calc
      _ ≤ δ * weightedPrimeReciprocalLogSum (fun _ => 1) N a b := h
      _ < δ * M := mul_lt_mul_of_pos_left honeBound hδ
      _ ≤ δ * K := mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt hδ)
      _ = ε / 3 := by
        dsimp [δ]
        field_simp [hK.ne']
  have hintApprox' :
      |(∫ x in a..b, Polynomial.eval x p / x) -
          ∫ x in a..b, f x / x| ≤ ε / 3 := by
    rw [abs_sub_comm]
    calc
      _ ≤ δ * J := hintApprox
      _ ≤ δ * K := mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hδ)
      _ = ε / 3 := by
        dsimp [δ]
        field_simp [hK.ne']
  calc
    |weightedPrimeReciprocalLogSum f N a b - ∫ x in a..b, f x / x| =
        |(weightedPrimeReciprocalLogSum f N a b -
            weightedPrimeReciprocalLogSum (Polynomial.eval · p) N a b) +
          (weightedPrimeReciprocalLogSum (Polynomial.eval · p) N a b -
            ∫ x in a..b, Polynomial.eval x p / x) +
          ((∫ x in a..b, Polynomial.eval x p / x) -
            ∫ x in a..b, f x / x)| := by ring_nf
    _ ≤ |weightedPrimeReciprocalLogSum f N a b -
            weightedPrimeReciprocalLogSum (Polynomial.eval · p) N a b| +
          |weightedPrimeReciprocalLogSum (Polynomial.eval · p) N a b -
            ∫ x in a..b, Polynomial.eval x p / x| +
          |(∫ x in a..b, Polynomial.eval x p / x) -
            ∫ x in a..b, f x / x| := by
      apply (abs_add_le _ _).trans
      gcongr
      exact abs_add_le _ _
    _ < ε := by linarith

/-! ## 2. Mertens' product formula -/

/-- The prime product: Π_{p ≤ x} (1 - 1/p). Unfolding this compatibility
definition exposes the filtered range used by existing sieve proofs. -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  ((range (x + 1)).filter Nat.Prime).prod (fun p => 1 - 1 / (p : ℝ))

/-- The Chen-local Euler product is definitionally the reusable ANT object. -/
theorem primeProduct_eq_analyticNumberTheory (x : ℕ) :
    primeProduct x = AnalyticNumberTheory.Mertens.primeProduct x := rfl

/-- **Mertens' product formula**: Π_{p ≤ x} (1 - 1/p) ~ e^(-γ) / log x.

The quantitative form here gives a constant C such that
|Π_{p ≤ x} (1 - 1/p) - e^(-γ) / log x| ≤ C / (log x)².

This is a central tool for estimating V(z). -/
theorem mertens_product_formula :
    ∃ C : ℝ,
      ∀ x : ℕ, 2 ≤ x →
        |primeProduct x - exp (-eulerMascheroniConstant) / log x| ≤
          C / (log x) ^ 2 := by
  obtain ⟨C, _hC, hbound⟩ :=
    AnalyticNumberTheory.Mertens.primeProduct_mertens_nat
  refine ⟨C, fun x hx => ?_⟩
  simpa only [primeProduct_eq_analyticNumberTheory] using hbound x hx

/-- Two-sided uniform bounds of order `1 / log x` for the Mertens product. -/
theorem primeProduct_asymptotic_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ x : ℕ, 2 ≤ x →
      c₁ / log x ≤ primeProduct x ∧ primeProduct x ≤ c₂ / log x := by
  let B := AnalyticNumberTheory.Mertens.mertensSecondConstant +
    AnalyticNumberTheory.Mertens.logarithmicCorrectionLimit
  have hinv : Tendsto (fun n : ℕ => 1 / log (n : ℝ)) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop 1
  obtain ⟨K, hK⟩ := isBigO_one_nat_atTop_iff.mp <|
    AnalyticNumberTheory.Mertens.log_primeProduct_mertens_isBigO.trans
      (hinv.isBigO_one (F := ℝ))
  refine ⟨exp (-K - B), exp (K - B), exp_pos _, ?_⟩
  intro n hn
  have hlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast Nat.one_lt_two.trans_le hn)
  have hP : 0 < primeProduct n := AnalyticNumberTheory.Mertens.primeProduct_pos n
  have hb : |log (primeProduct n * log n) + B| ≤ K := by
    rw [Real.log_mul hP.ne' hlog.ne']
    exact hK n
  have hlo := (abs_le.mp hb).1
  have hhi := (abs_le.mp hb).2
  refine ⟨(div_le_iff₀ hlog).mpr ?_, (le_div_iff₀ hlog).mpr ?_⟩
  · rw [← Real.exp_log (mul_pos hP hlog)]
    exact exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_log (mul_pos hP hlog)]
    exact exp_le_exp.mpr (by linarith)

/-- **Mertens product lower bound**: there is `cpp > 0` such that, for every `m ≥ 3`,
  `cpp / log m ≤ primeProduct m`.

This follows directly from `primeProduct_asymptotic_order`, which gives
`c₁/log x ≤ primeProduct x` for every `x ≥ 2`. It is one of the two standard
inputs to the main-term lower bound `CorrectedChenMainTermLower`. -/
theorem primeProduct_lower_bound :
    ∃ cpp : ℝ, 0 < cpp ∧ ∀ m : ℕ, 3 ≤ m → cpp / log m ≤ primeProduct m := by
  obtain ⟨c₁, _c₂, hc₁, hbound⟩ := primeProduct_asymptotic_order
  refine ⟨c₁, hc₁, fun m hm => ?_⟩
  exact (hbound m (by omega)).1

/-- Existentially named form of `primeProduct_lower_bound`, for clients that
choose a fixed lower-bound constant. -/
theorem primeProduct_lower_bound_exists :
    ∃ cpp : ℝ, 0 < cpp ∧ ∀ m : ℕ, 3 ≤ m → cpp / log m ≤ primeProduct m :=
  primeProduct_lower_bound

/-- **Lemma 1 (Liu 2022)**: for fixed 0 < α < β, the sum
Σ_{x^α < p ≤ x^β} 1/p is bounded.

By Mertens' second theorem,
  Σ_{x^α < p ≤ x^β} 1/p = (log log x^β + B₁ + O(1/log x)) - (log log x^α + B₁ + O(1/log x))
                       = log(β/α) + O(1/log x)

Thus the sum is bounded, as is the further truncation to p ≤ x used here. -/
theorem prime_reciprocal_sum_bounded (α β : ℝ) (hα : 0 < α) (_hβ : α < β) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |((range (x + 1)).filter (fun p => Nat.Prime p ∧
        ((x : ℝ) ^ α < (p : ℝ) ∧ (p : ℝ) ≤ (x : ℝ) ^ β))).sum
        (fun p => 1 / (p : ℝ))| ≤ C := by
  have hlim := tendsto_weightedPrimeReciprocalLogSum_const (c := 1) hα _hβ
  obtain ⟨C, hC⟩ := isBigO_one_nat_atTop_iff.mp (hlim.isBigO_one (F := ℝ))
  refine ⟨C, fun x _ => ?_⟩
  let T := (range (x + 1)).filter fun p : ℕ => Nat.Prime p ∧
    ((x : ℝ) ^ α < (p : ℝ) ∧ (p : ℝ) ≤ (x : ℝ) ^ β)
  have hsub : T ⊆ (Ioc (rpowFloor x α) (rpowFloor x β)).filter Nat.Prime := by
    intro p hp
    have h := (mem_filter.mp hp).2
    exact mem_filter.mpr ⟨(mem_Ioc_rpowFloor_iff).mpr h.2, h.1⟩
  change |∑ p ∈ T, 1 / (p : ℝ)| ≤ C
  rw [abs_of_nonneg (sum_nonneg fun p _ => by positivity)]
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans ?_
  change weightedPrimeReciprocalLogSum (fun _ => 1) x α β ≤ C
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x)

/-! ## 4. Application: an asymptotic formula for the sieve product V(z) -/

/-- Goldbach sieve product V(z, N) = Π_{p < z, p ∤ N} (1 - 1/(p-1)). -/
noncomputable def goldbachSieveProduct (N z : ℕ) : ℝ :=
  ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1))


/-- **Sieve-product identity**: V(z,N) = Π_{p<z}(1-1/p) · 𝔖(N,z-1).

For odd primes, factor (1-1/(p-1)) = (1-1/p)(1-1/(p-1)²). Then:
  - if p ∤ N (which excludes p = 2 for even N),
    (1-1/p)·localFactor(p,N) = 1-1/(p-1);
  - if p | N (including p = 2, since N is even),
    (1-1/p)·localFactor(p,N) = 1.
Thus Π_{p<z}(1-1/p)·𝔖(N,z-1) = Π_{p<z}[(1-1/p)·localFactor(p,N)] = V.

This is the exact identity underlying V ≈ 𝔖(N)·e^{-γ}/log z. -/
theorem sieveProduct_identity (N z : ℕ) (hz : 2 ≤ z) (hN : Even N) :
    goldbachSieveProduct N z =
      primeProduct (z - 1) * SingularSeries.singularSeriesTruncated N (z - 1) := by
  have hz1 : 1 ≤ z := by omega
  have h2dvd : 2 ∣ N := by
    rcases hN with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  have hrangeP : (range (z - 1 + 1)).filter Nat.Prime = (range z).filter Nat.Prime := by
    rw [Nat.sub_add_cancel hz1]
  unfold goldbachSieveProduct primeProduct SingularSeries.singularSeriesTruncated
    AnalyticNumberTheory.Sieve.singularSeriesTruncated
  simp only [Nat.primesLE_eq_filter_range, hrangeP]
  change _ = ((range z).filter Nat.Prime).prod (fun p => 1 - 1 / (p : ℝ)) *
    ((range z).filter Nat.Prime).prod (fun p => SingularSeries.localFactor p N)
  -- Goal: ∏_{p<z,p∤N}(1-1/(p-1)) = ∏_{p<z}(1-1/p) · ∏_{p<z} localFactor p N.
  rw [← Finset.prod_mul_distrib]
  -- Split according to p | N or p ∤ N.
  have hpart : ((range z).filter Nat.Prime) =
      ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)) ∪
      ((range z).filter (fun p => Nat.Prime p ∧ p ∣ N)) := by
    ext p
    simp only [mem_filter, mem_union, mem_range]
    by_cases hp : p ∣ N <;> simp [hp]
  have hdisj : Disjoint ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N))
      ((range z).filter (fun p => Nat.Prime p ∧ p ∣ N)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [mem_filter] at hp1 hp2
    exact hp1.2.2 hp2.2.2
  rw [hpart, Finset.prod_union hdisj]
  -- Factorwise: p ∤ N ⟹ (1-1/p)·localFactor = 1-1/(p-1).
  have hF_pnd : ∀ p ∈ (range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N),
      1 - 1 / ((p : ℝ) - 1) =
        (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N := by
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2.1
    have hpnd : ¬ p ∣ N := (mem_filter.mp hp).2.2
    have hpne2 : p ≠ 2 := by
      intro hp2
      exact hpnd (by simpa [hp2] using h2dvd)
    unfold SingularSeries.localFactor AnalyticNumberTheory.Sieve.localFactor
    rw [ite_eq_right hpne2, ite_eq_right hpnd]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
      have : 0 < (p : ℝ) - 1 := by linarith
      exact ne_of_gt this
    field_simp [hp0, hpm1]
    ring
  -- Factorwise: p | N ⟹ (1-1/p)·localFactor = 1.
  have hF_pd : ∀ p ∈ (range z).filter (fun p => Nat.Prime p ∧ p ∣ N),
      (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N = 1 := by
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2.1
    have hpd : p ∣ N := (mem_filter.mp hp).2.2
    unfold SingularSeries.localFactor AnalyticNumberTheory.Sieve.localFactor
    by_cases hp2 : p = 2
    · subst hp2
      rw [ite_eq_left rfl, ite_eq_left h2dvd]
      norm_num
    · rw [ite_eq_right hp2, ite_eq_left hpd]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
        have : 0 < (p : ℝ) - 1 := by linarith
        exact ne_of_gt this
      field_simp [hp0, hpm1]
  -- Combine the factor identities.
  have hLHS : ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1)) =
      ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
        (fun p => (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N) :=
    Finset.prod_congr rfl hF_pnd
  have hRHS : ((range z).filter (fun p => Nat.Prime p ∧ p ∣ N)).prod
        (fun p => (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N) = 1 :=
    Finset.prod_eq_one hF_pd
  rw [hLHS, hRHS, mul_one]


/-! ## 4.5 Sums of 1/(p-1) over primes (for Selberg Lemma 2) -/

/-- Σ_{p ≤ y} 1/p² is bounded by a constant depending only on Σ_{n≥1} 1/n². -/
theorem prime_inv_sq_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℕ, ((range (y + 1)).filter Nat.Prime).sum
      (fun p => 1 / (p : ℝ) ^ 2) ≤ K := by
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)
  refine ⟨∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ), tsum_nonneg (fun n => by positivity), ?_⟩
  intro y
  exact Summable.sum_le_tsum ((range (y + 1)).filter Nat.Prime) (fun n _hn => by positivity) hsum2

/-- Σ_{p ≤ y} 1/(p-1) ≤ log(log y) + C for y ≥ 3,
by Mertens' second theorem and a decomposition of each summand. -/
theorem prime_inv_pminus1_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ, 3 ≤ y →
      ((range (y + 1)).filter Nat.Prime).sum
        (fun p => 1 / ((p : ℝ) - 1)) ≤ log (log y) + C := by
  obtain ⟨C, hC, hM⟩ := AnalyticNumberTheory.Mertens.mertensSecond_nat
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_bound
  let B := AnalyticNumberTheory.Mertens.mertensSecondConstant
  let D := B + C / log 2 + 2 * K
  refine ⟨max D 0, le_max_right _ _, fun y hy => ?_⟩
  have hy2 : 2 ≤ y := by omega
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hyR
  have hCdiv := div_le_div_of_nonneg_left hC.le (Real.log_pos one_lt_two) hlog
  have hMupper := (abs_le.mp (hM y hy2)).2
  have hsum : (∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)) ≤
      primeReciprocalSum y + 2 * K := by
    calc
      _ ≤ ∑ p ∈ (range (y + 1)).filter Nat.Prime,
          (1 / (p : ℝ) + 2 * (1 / (p : ℝ) ^ 2)) := by
        apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
        have hp0 : 0 < (p : ℝ) := by linarith
        have hpm : 0 < (p : ℝ) - 1 := by linarith
        have hden : (p : ℝ) ^ 2 / 2 ≤ p * ((p : ℝ) - 1) := by
          nlinarith [mul_nonneg hp0.le (show (0 : ℝ) ≤ p - 2 by linarith)]
        calc
          _ = 1 / (p : ℝ) + 1 / (p * ((p : ℝ) - 1)) := by
            field_simp
            ring
          _ ≤ 1 / (p : ℝ) + 1 / ((p : ℝ) ^ 2 / 2) := by
            gcongr
          _ = _ := by ring
      _ ≤ primeReciprocalSum y + 2 * K := by
        rw [sum_add_distrib, ← mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hK y) (by norm_num))
  change _ ≤ log (log y) + max D 0
  change primeReciprocalSum y - (log (log y) + B) ≤ C / log y at hMupper
  dsimp [D]
  linarith only [hCdiv, hMupper, hsum, le_max_left D 0]

/-- **Sieve-product asymptotic formula**:
V(z, N) ≈ 𝔖(N, z-1) · e^(-γ) / log(z-1).

Here 𝔖(N, z) = Π_{p ≤ z, p.Prime} localFactor(p, N) is the truncated
singular series (`SingularSeries.singularSeriesTruncated`).

The singular-series factor cannot be omitted: N with many small odd prime
factors contribute local corrections p/(p-1) that are not uniformly bounded.
The asymptotic V ≈ 𝔖(N)·e^{-γ}/log z follows from
(1 - 1/(p-1)) = (1 - 1/p)·(1 - 1/(p-1)²) at odd primes and Mertens' product
formula. It underlies the calculation of the Jurkat-Richert main term X · V(z).

The error must also be multiplied by the truncated singular series to obtain
a consequence of Mertens' product formula uniform in N. The cutoff `z - 1`
corresponds exactly to the range `p < z` in `goldbachSieveProduct`. -/
theorem sieve_product_asymptotic :
    ∃ C : ℝ,
      ∀ N z : ℕ, 3 ≤ z → Even N → 4 ≤ N →
        |goldbachSieveProduct N z -
          SingularSeries.singularSeriesTruncated N (z - 1) *
            exp (-eulerMascheroniConstant) / log ((z - 1 : ℕ) : ℝ)| ≤
          C * SingularSeries.singularSeriesTruncated N (z - 1) /
            (log ((z - 1 : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C, hC⟩ := mertens_product_formula
  refine ⟨C, ?_⟩
  intro N z hz hN _hN4
  have hz2 : 2 ≤ z - 1 := by omega
  have hz1 : 1 ≤ z - 1 := by omega
  have hP := hC (z - 1) hz2
  have hSpos : 0 < SingularSeries.singularSeriesTruncated N (z - 1) :=
    SingularSeries.singularSeriesTruncated_pos N (z - 1) hz1
  rw [sieveProduct_identity N z (by omega) hN]
  have hmul := mul_le_mul_of_nonneg_right hP (le_of_lt hSpos)
  calc
    |primeProduct (z - 1) * SingularSeries.singularSeriesTruncated N (z - 1) -
        SingularSeries.singularSeriesTruncated N (z - 1) *
          exp (-eulerMascheroniConstant) / log ((z - 1 : ℕ) : ℝ)| =
        |primeProduct (z - 1) - exp (-eulerMascheroniConstant) /
          log ((z - 1 : ℕ) : ℝ)| *
          SingularSeries.singularSeriesTruncated N (z - 1) := by
            rw [show primeProduct (z - 1) *
                SingularSeries.singularSeriesTruncated N (z - 1) -
              SingularSeries.singularSeriesTruncated N (z - 1) *
                exp (-eulerMascheroniConstant) / log ((z - 1 : ℕ) : ℝ) =
              (primeProduct (z - 1) - exp (-eulerMascheroniConstant) /
                log ((z - 1 : ℕ) : ℝ)) *
                SingularSeries.singularSeriesTruncated N (z - 1) by ring,
              abs_mul, abs_of_pos hSpos]
    _ ≤ C / (log ((z - 1 : ℕ) : ℝ)) ^ 2 *
          SingularSeries.singularSeriesTruncated N (z - 1) := hmul
    _ = C * SingularSeries.singularSeriesTruncated N (z - 1) /
          (log ((z - 1 : ℕ) : ℝ)) ^ 2 := by ring

/-! ## 5. Auxiliary lemmas: the prime-counting function -/


/-! ## 6. The twin-prime constant and a finite truncation -/


/-! ## 6.5 Local interval factors -/

/-- Positivity of the Goldbach local factor, independently of the prime carrier. -/
private lemma goldbach_local_factor_pos {p : ℕ} (hp2 : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- For an odd prime, the logarithm of the inverse Goldbach local factor is
controlled by its reciprocal-prime main term and a summable error. -/
private lemma log_goldbach_inverse_factor_le {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    log (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      1 / (p : ℝ) + 12 / (p : ℝ) ^ 2 := by
  have hp3 : 3 ≤ p := by omega
  have hpm1 : 0 < (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have ht : 0 < 1 / ((p : ℝ) - 1) := div_pos one_pos hpm1
  have htle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    linarith
  have hlocal := AnalyticNumberTheory.Mertens.abs_log_one_sub_add_le ht htle
  have hlog :
      log (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        1 / ((p : ℝ) - 1) + 2 * (1 / ((p : ℝ) - 1)) ^ 2 := by
    rw [Real.log_inv]
    have := (abs_le.mp hlocal).1
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm1
  have hmain :
      1 / ((p : ℝ) - 1) + 2 * (1 / ((p : ℝ) - 1)) ^ 2 ≤
        1 / (p : ℝ) + 12 / (p : ℝ) ^ 2 := by
    have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    field_simp [hp0, hpm1ne]
    nlinarith [sq_nonneg ((p : ℝ) - 3)]
  exact hlog.trans hmain

/-- A quantitative interval form of Mertens' second theorem for inverse
Goldbach local factors.  The error has the sharp inverse-logarithmic shape
needed by the dimension-one sieve hypothesis. -/
theorem exists_log_goldbach_inverse_interval_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k n : ℕ, 2 ≤ k → k ≤ n →
      ∀ s : Finset ℕ,
        (∀ p ∈ s, p.Prime ∧ k < p ∧ p ≤ n) →
        log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
          log (log n / log k) + (2 * C + 24) / log k := by
  obtain ⟨C, hC, hM⟩ := AnalyticNumberTheory.Mertens.mertensSecond_nat
  refine ⟨C, hC.le, ?_⟩
  intro k n hk hkn s hs
  have hkR : (1 : ℝ) < k := by exact_mod_cast Nat.one_lt_two.trans_le hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans hkR
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hlogk := Real.log_pos hkR
  have hlogkn := Real.log_le_log hk0 hknR
  have hlogn := hlogk.trans_le hlogkn
  let T := (Finset.Ioo k (n + 1)).filter Nat.Prime
  have hsub : s ⊆ T := by
    intro p hp
    rcases hs p hp with ⟨hpp, hkp, hpn⟩
    exact mem_filter.mpr ⟨mem_Ioo.mpr ⟨hkp, Nat.lt_succ_of_le hpn⟩, hpp⟩
  have hlogprod :
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
        ∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Real.log_prod
    intro p hp
    exact (inv_pos.mpr (goldbach_local_factor_pos
      (lt_of_le_of_lt hk (hs p hp).2.1))).ne'
  have hlocal :
      (∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
        (∑ p ∈ s, (1 / (p : ℝ) + 12 / (p : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact log_goldbach_inverse_factor_le (hs p hp).1
      (lt_of_le_of_lt hk (hs p hp).2.1)
  have hT : T = n.primesLE \ k.primesLE := by
    apply Finset.ext
    intro p
    simp only [T, Finset.mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Ioo, Nat.lt_succ_iff]
    by_cases hp : p.Prime <;> simp [hp, not_le, and_comm]
  have hrecip : (∑ p ∈ s, 1 / (p : ℝ)) ≤
      primeReciprocalSum n - primeReciprocalSum k := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => 1 / (p : ℝ))
      hsub (fun p _ _ => by positivity)
    rwa [hT, Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hkn)] at hsum
  have hMrecip : primeReciprocalSum n - primeReciprocalSum k ≤
      log (log n / log k) + 2 * C / log k := by
    have hupper := (abs_le.mp (hM n (hk.trans hkn))).2
    have hlower := (abs_le.mp (hM k hk)).1
    have hCdiv := div_le_div_of_nonneg_left hC.le hlogk hlogkn
    rw [Real.log_div hlogn.ne' hlogk.ne', mul_div_assoc, two_mul]
    change primeReciprocalSum n - _ ≤ _ at hupper
    change _ ≤ primeReciprocalSum k - _ at hlower
    linarith only [hupper, hlower, hCdiv]
  have hsq :
      (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤ 2 / (k : ℝ) := by
    calc
      (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Ioo k (n + 1), 1 / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => (Finset.mem_filter.mp (hsub hp)).1)
          (fun p _ _ => by positivity)
      _ ≤ 2 / ((k : ℝ) + 1) := by
        simpa only [one_div] using (sum_Ioo_inv_sq_le (α := ℝ) k (n + 1))
      _ ≤ 2 / (k : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num)
        positivity
        linarith
  have h24 : (24 : ℝ) / k ≤ 24 / log k :=
    div_le_div_of_nonneg_left (by norm_num) hlogk (Real.log_le_self hk0.le)
  calc
    log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
        ∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹ := hlogprod
    _ ≤ ∑ p ∈ s, (1 / (p : ℝ) + 12 / (p : ℝ) ^ 2) := hlocal
    _ = (∑ p ∈ s, 1 / (p : ℝ)) + 12 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib]
      congr 1
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (primeReciprocalSum n - primeReciprocalSum k) +
        12 * (2 / (k : ℝ)) :=
      add_le_add (hrecip) (mul_le_mul_of_nonneg_left hsq (by norm_num))
    _ ≤ log (log n / log k) + (2 * C + 24) / log k := by
      rw [add_div, show (12 : ℝ) * (2 / k) = 24 / k by ring]
      linarith only [hMrecip, h24]

/-- The inverse Goldbach local factors on an arbitrary real interval satisfy the
standard dimension-one product bound. -/
theorem exists_goldbach_inverse_interval_bound :
    ∃ K : ℝ, 1 < K ∧ ∀ s : Finset ℕ,
      (∀ p ∈ s, p.Prime ∧ 2 < p) →
      ∀ z₁ z₂ : ℝ, 2 ≤ z₁ → z₁ ≤ z₂ →
        (∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) →
        (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
          log z₂ / log z₁ * (1 + K / log z₁) := by
  obtain ⟨C, hC, hinterval⟩ := exists_log_goldbach_inverse_interval_bound
  let A : ℝ := 2 * C + 24
  let D : ℝ := 2 * A + 2 * log 2
  let K : ℝ := D * exp (D / log 2) + 2
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hC]
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 1 < K := by
    have : 0 < D * exp (D / log 2) := mul_pos hD (Real.exp_pos _)
    dsimp [K]
    linarith only [this]
  refine ⟨K, hK, ?_⟩
  intro s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  have hz₁pos : 0 < z₁ := by linarith only [hz₁]
  have hz₂pos : 0 < z₂ := hz₁pos.trans_le hz₁₂
  have hlogz₁ : 0 < log z₁ := Real.log_pos (by linarith only [hz₁])
  have hlogz₁₂ : log z₁ ≤ log z₂ := Real.log_le_log hz₁pos hz₁₂
  have hlogz₂ : 0 < log z₂ := hlogz₁.trans_le hlogz₁₂
  have hratio_pos : 0 < log z₂ / log z₁ := div_pos hlogz₂ hlogz₁
  -- One cutoff works on the entire real range, including z₁ = 2.
  -- The ceiling predecessor retains a prime at the closed lower endpoint;
  -- the maximum with 2 is harmless because every prime in s is odd.
  let k : ℕ := max 2 (Nat.ceil z₁ - 1)
  let n : ℕ := max k (Nat.floor z₂)
  have hk2 : 2 ≤ k := le_max_left _ _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hceil1 : 1 ≤ Nat.ceil z₁ := by
    have := Nat.le_ceil z₁
    by_contra h
    have : Nat.ceil z₁ = 0 := by omega
    simp only [this, Nat.cast_zero] at *
    linarith
  have hpredcast : ((Nat.ceil z₁ - 1 : ℕ) : ℝ) = (Nat.ceil z₁ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1, Nat.cast_one]
  have hklez₁ : (k : ℝ) ≤ z₁ := by
    dsimp [k]
    rw [Nat.cast_max, max_le_iff, hpredcast]
    exact ⟨hz₁, by linarith only [Nat.ceil_lt_add_one hz₁pos.le]⟩
  have hz₁lek : z₁ ≤ (k : ℝ) + 1 := by
    have hpred : (Nat.ceil z₁ : ℝ) - 1 ≤ (k : ℝ) := by
      rw [← hpredcast]
      exact_mod_cast (le_max_right 2 (Nat.ceil z₁ - 1))
    linarith [Nat.le_ceil z₁]
  have hkhalf : z₁ / 2 ≤ (k : ℝ) := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith only [this, hz₁lek]
  have hnlez₂ : (n : ℝ) ≤ z₂ := by
    dsimp [n]
    rw [Nat.cast_max, max_le_iff]
    exact ⟨hklez₁.trans hz₁₂, Nat.floor_le hz₂pos.le⟩
  have hkn : k ≤ n := le_max_left _ _
  have hlogk : 0 < log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlogn : 0 < log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hbound := hinterval k n hk2 hkn s (by
    intro p hp
    refine ⟨(hs p hp).1, ?_, ?_⟩
    · have hceil : Nat.ceil z₁ ≤ p := Nat.ceil_le.mpr (hsinterval p hp).1
      have hp2 := (hs p hp).2
      dsimp [k]
      omega
    · exact (Nat.le_floor (hsinterval p hp).2.le).trans (le_max_right _ _))
  -- k ≥ 2 and z₁ ≤ k + 1 imply z₁ ≤ k², so the logarithmic
  -- comparison needs no large/small split or auxiliary exponential threshold.
  have hlogk_half : log z₁ / 2 ≤ log (k : ℝ) := by
    have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hz₁sq : z₁ ≤ (k : ℝ) ^ 2 := by nlinarith only [hk2r, hz₁lek]
    have h := Real.log_le_log hz₁pos hz₁sq
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hlogk_lower : log z₁ - log 2 ≤ log (k : ℝ) := by
    calc
      log z₁ - log 2 = log (z₁ / 2) :=
        (Real.log_div hz₁pos.ne' (by norm_num)).symm
      _ ≤ log (k : ℝ) := Real.log_le_log (by positivity) hkhalf
  have hAdiv : A / log (k : ℝ) ≤ 2 * A / log z₁ := by
    apply (div_le_div_iff₀ hlogk hlogz₁).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlogk_half hA]
  have hlogratio : log (log z₁ / log (k : ℝ)) ≤ 2 * log 2 / log z₁ := by
    calc
      log (log z₁ / log (k : ℝ)) ≤ log z₁ / log (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hlogz₁ hlogk)
      _ = (log z₁ - log (k : ℝ)) / log (k : ℝ) := by field_simp
      _ ≤ log 2 / log (k : ℝ) :=
        div_le_div_of_nonneg_right (by linarith only [hlogk_lower]) hlogk.le
      _ ≤ 2 * log 2 / log z₁ := by
        apply (div_le_div_iff₀ hlogk hlogz₁).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hlogk_half hlog2.le]
  have hinner : log (log (n : ℝ) / log (k : ℝ)) ≤
      log (log z₂ / log (k : ℝ)) :=
    Real.log_le_log (div_pos hlogn hlogk)
      (div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) hnlez₂) hlogk.le)
  have hsplit : log (log z₂ / log (k : ℝ)) =
      log (log z₂ / log z₁) + log (log z₁ / log (k : ℝ)) := by
    rw [Real.log_div hlogz₂.ne' hlogk.ne',
      Real.log_div hlogz₂.ne' hlogz₁.ne', Real.log_div hlogz₁.ne' hlogk.ne']
    ring
  have hlogprod : log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log (log z₂ / log z₁) + D / log z₁ := by
    calc
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
          log (log (n : ℝ) / log (k : ℝ)) + A / log (k : ℝ) := hbound
      _ ≤ log (log z₂ / log (k : ℝ)) + 2 * A / log z₁ :=
        add_le_add hinner hAdiv
      _ ≤ log (log z₂ / log z₁) +
          (2 * log 2 / log z₁ + 2 * A / log z₁) := by
        rw [hsplit]
        linarith only [hlogratio]
      _ = log (log z₂ / log z₁) + D / log z₁ := by dsimp [D]; ring
  -- Linearize exp on the fixed compact range 0 ≤ D/log z₁ ≤ D/log 2.
  -- Its tangent inequality at -x gives exp x ≤ 1 + x * exp x.
  have hx : 0 ≤ D / log z₁ := by positivity
  have hxupper : D / log z₁ ≤ D / log 2 :=
    div_le_div_of_nonneg_left hD.le hlog2
      (Real.log_le_log (by norm_num) hz₁)
  have hexp : exp (D / log z₁) ≤ 1 + K / log z₁ := by
    have htangent := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (-(D / log z₁))) (Real.exp_pos (D / log z₁)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at htangent
    have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxupper) hx
    calc
      exp (D / log z₁) ≤ 1 + (D / log z₁) * exp (D / log 2) := by
        nlinarith only [htangent, hmul]
      _ ≤ 1 + K / log z₁ := by
        have hKdiv : K / log z₁ =
            (D / log z₁) * exp (D / log 2) + 2 / log z₁ := by
          dsimp only [K]
          ring
        rw [hKdiv]
        have hslack : 0 ≤ (2 : ℝ) / log z₁ := by positivity
        linarith only [hslack]
  have hprodpos : 0 < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2))
  have hprodexp := Real.exp_le_exp.mpr hlogprod
  rw [Real.exp_log hprodpos, Real.exp_add, Real.exp_log hratio_pos] at hprodexp
  exact hprodexp.trans (mul_le_mul_of_nonneg_left hexp hratio_pos.le)

/-- **Sieve-product lower bound**: there is c₁ > 0 such that, for every
 even N ≥ 4 and z ≥ 2, `c₁ / log z ≤ goldbachSieveProduct N z`.
 Specialize the finite-set inverse interval estimate to `[2,z)` and invert. -/
theorem goldbachSieveProduct_lower_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ N z : ℕ, 2 ≤ z → Even N → 4 ≤ N →
      c₁ / log z ≤ goldbachSieveProduct N z := by
  obtain ⟨K, hK, hinterval⟩ := exists_goldbach_inverse_interval_bound
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hfactor : 0 < 1 + K / log 2 := by positivity
  refine ⟨log 2 / (1 + K / log 2), div_pos hlog2 hfactor, ?_⟩
  intro N z hz hN _hN4
  let s := (range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    refine ⟨hp'.1, ?_⟩
    have h2 : 2 ∣ N := even_iff_two_dvd.mp hN
    have hp2 : p ≠ 2 := by
      intro heq
      exact hp'.2 (heq.symm ▸ h2)
    have := hp'.1.two_le
    omega
  have hVpos : 0 < goldbachSieveProduct N z :=
    Finset.prod_pos (fun p hp => goldbach_local_factor_pos (hs p hp).2)
  have hbound := hinterval s hs 2 z (by norm_num) (by exact_mod_cast hz) (by
    intro p hp
    constructor
    · exact_mod_cast (hs p hp).1.two_le
    · exact_mod_cast (mem_range.mp (mem_filter.mp hp).1))
  have hlogz : 0 < log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hRpos : 0 < log (z : ℝ) / log 2 * (1 + K / log 2) :=
    mul_pos (div_pos hlogz hlog2) hfactor
  rw [Finset.prod_inv_distrib] at hbound
  change (goldbachSieveProduct N z)⁻¹ ≤ _ at hbound
  have hinv := one_div_le_one_div_of_le (inv_pos.mpr hVpos) hbound
  have heq : log 2 / (1 + K / log 2) / log (z : ℝ) =
      1 / (log (z : ℝ) / log 2 * (1 + K / log 2)) := by
    field_simp
  rw [heq]
  simpa only [one_div, inv_inv] using hinv

/-! ## 7. Mathematical scope -/

/-
**Mertens' theorems and their applications**:

1. **Analytic theorems**:
   - `mertens_second_theorem`: Σ 1/p = log log x + B₁ + O(1/log x)
   - `mertens_product_formula`: Π (1-1/p) ~ e^(-γ)/log x
   - `prime_number_theorem`: π(x) ~ x/log x

2. **Applications**:
   - `prime_reciprocal_sum_bounded`: Lemma 1, bounded prime-reciprocal sums
   - `sieve_product_asymptotic`: V(z,N) ≈ 𝔖(N,z-1) e^(-γ)/log(z-1),
     with the truncated singular-series factor also present in the error

3. **Finite twin-prime product**:
   - `twinPrimeConstant`: legacy finite truncation of Π_{p>2} (1 - 1/(p-1)²)
   - `twinPrimeConstant_pos`: positivity of the finite product
   - `twinPrimeConstant_lt_one`: the finite product is less than 1

4. **Dependencies**:
   - The three principal analytic theorems use the interfaces supplied by
     `analytic-number-theory-lean`.
   - Definitional bridges give the local statements; `Audit.lean` is the
     repository's entry point for inspecting theorem dependencies.
   - The local proofs are explicit derivations from these imported results,
     not additional analytic assumptions.
-/

end MathlibNt.SieveTheory.MertensTheorem
