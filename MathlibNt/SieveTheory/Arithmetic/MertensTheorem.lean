import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import AnalyticNumberTheory
import MathlibNt.SieveTheory.Arithmetic.SingularSeries

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

namespace MathlibNt.SieveTheory.MertensTheorem

open Filter Real Finset
open scoped Topology

/-! ## 1. Mertens' second theorem -/

/-- The sum of prime reciprocals: Σ_{p ≤ x} 1/p. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  ((range (x + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ))

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
  unfold primeReciprocalCoeff primeReciprocalSum
  rw [← Nat.range_succ_eq_Icc_zero n]
  rw [← Finset.sum_filter]

/-- Derivative of a test function pulled back to logarithmic scale. -/
private noncomputable def logScaleDeriv (f' : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
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
    field_simp [hlogN]
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
private theorem tendsto_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rpowFloor N a) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

private theorem eventually_two_le_rpowFloor {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ rpowFloor N a :=
  (tendsto_rpowFloor_atTop ha).eventually (eventually_ge_atTop 2)

/-- Flooring changes a positive real power by a relative error tending to zero. -/
private theorem tendsto_rpowFloor_div_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (rpowFloor N a : ℝ) / ((N : ℝ) ^ a))
      atTop (nhds 1) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N : ℕ => 1 - 1 / ((N : ℝ) ^ a))
      atTop (nhds 1) := by
    simpa using (hpow.const_div_atTop 1).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [hpow.eventually (eventually_gt_atTop 0)] with N hpos
    have hfloorlt : ((N : ℝ) ^ a) < (rpowFloor N a : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one ((N : ℝ) ^ a)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
    simpa only [one_mul] using le_of_lt hfloorlt
  · filter_upwards [hpow.eventually (eventually_gt_atTop 0)] with N hpos
    rw [div_le_one hpos]
    exact Nat.floor_le (le_of_lt hpos)

private theorem tendsto_log_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => log (rpowFloor N a : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_rpowFloor_atTop ha))

private theorem tendsto_log_rpowFloor_sub_log_rpow {a : ℝ} (ha : 0 < a) :
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
private theorem tendsto_log_log_rpowFloor_sub {a : ℝ} (ha : 0 < a) :
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

/-- A fixed finite linear combination of constant logarithmic cells converges
to the same linear combination of logarithmic masses. -/
theorem tendsto_finset_weightedPrimeReciprocalLogSum_const
    {ι : Type*} (s : Finset ι) (c a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i < b i) :
    Tendsto
      (fun N : ℕ => ∑ i ∈ s,
        weightedPrimeReciprocalLogSum (fun _ => c i) N (a i) (b i))
      atTop
      (nhds (∑ i ∈ s, c i * log (b i / a i))) := by
  refine tendsto_finsetSum s ?_
  intro i hi
  exact tendsto_weightedPrimeReciprocalLogSum_const (ha i hi) (hab i hi)

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
  calc
    (∫ x in a..b, f x / x) = ∫ x in a..b, f x * (1 / x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = _ := hparts

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

/-- The prime product: Π_{p ≤ x} (1 - 1/p). -/
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

/-- General local logarithmic correction: for 0 < t ≤ 1/2,
|log(1 - t) + t| ≤ 2t².

The inequality `log x ≤ x - 1` gives log(1-t) ≤ -t.
The inequality `log(1/(1-t)) ≤ t/(1-t)`, equivalently
`log(1-t) ≥ -t/(1-t)`, together with t ≤ 1/2 gives the lower bound. -/
private lemma log_one_sub_bound {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  -- Upper bound: log(1 - t) ≤ -t.
  have hub : log (1 - t) ≤ -t := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  -- Lower bound: log(1 - t) ≥ -t - 2t².
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec : 0 < 1 / (1 - t) := by positivity
    have hle := Real.log_le_sub_one_of_pos hrec
    -- log(1/(1-t)) ≤ t/(1-t), and log(1/(1-t)) = -log(1-t).
    have hloginv : log (1 / (1 - t)) = -log (1 - t) := by
      rw [one_div, Real.log_inv]
    have hle' : -log (1 - t) ≤ t / (1 - t) := by
      have hstep : 1 / (1 - t) - 1 = t / (1 - t) := by
        field_simp [hne]
        ring
      rwa [hloginv, hstep] at hle
    have hsame : -(t / (1 - t)) = -t / (1 - t) := by
      rw [div_eq_mul_inv, ← neg_mul, ← div_eq_mul_inv]
    have hge0 : -t / (1 - t) ≤ log (1 - t) := by
      have h := neg_le_neg hle'
      simpa [hsame] using h
    -- 1/(1-t) ≤ 1 + 2t when t ≤ 1/2.
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      have hx := mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hx
    have hneg : -t - 2 * t ^ 2 ≤ -t / (1 - t) := by
      calc -t - 2 * t ^ 2 ≤ -t * (1 + 2 * t) := by
            have hx : t * (1 + 2 * t) = t + 2 * t ^ 2 := by ring
            linarith
        _ ≤ -t / (1 - t) := by
          have h := neg_le_neg_iff.mpr hmul
          have hsame1 : -(t * (1 + 2 * t)) = -t * (1 + 2 * t) := by
            rw [← neg_mul]
          rwa [hsame1, hsame] at h
    linarith
  -- Combine the bounds: |log(1-t) + t| ≤ 2t².
  have hge : -2 * t ^ 2 ≤ log (1 - t) + t := by nlinarith [hlb]
  have hle0 : log (1 - t) + t ≤ 0 := by linarith [hub]
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Local logarithmic correction for each prime p ≥ 2:
|log(1 - 1/p) + 1/p| ≤ 2/p². -/
private lemma log_one_sub_prime_bound {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  let t : ℝ := 1 / (p : ℝ)
  have ht0 : 0 < t := by
    unfold t
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : t ≤ 1 / 2 := by
    unfold t
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp.two_le)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsubst : |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| = |log (1 - t) + t| := by
    simp [t]
  have hrhs : 2 * t ^ 2 = 2 / (p : ℝ) ^ 2 := by
    unfold t
    field_simp [hp0]
  rw [hsubst, ← hrhs]
  exact log_one_sub_bound ht0 htle

/-- **Order form of Mertens' product formula**: primeProduct x = Θ(1/log x);
there are positive constants c₁, c₂ such that
c₁/log x ≤ Π_{p ≤ x}(1 - 1/p) ≤ c₂/log x.

This weaker version of `mertens_product_formula`, which has the exact constant
e^{-γ}, follows directly from Mertens' second theorem via
-log Π = Σ 1/p + O(1). It does not require the Euler-Mascheroni constant identity.
Proof outline:
  1. log Π = Σ log(1 - 1/p), and |log(1 - 1/p) + 1/p| ≤ 2/p².
  2. Thus -log Π = Σ 1/p + E(x), with
     |E(x)| ≤ Σ 2/p² ≤ 2·Σ_{n≥1} 1/n² < ∞.
  3. Mertens' second theorem gives Σ 1/p = log log x + B₁ + O(1/log x).
  4. Hence Π = exp(-B₁ - δ - E)/log x, where |δ| and |E| are bounded,
     so Π = Θ(1/log x). -/
theorem primeProduct_asymptotic_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ x : ℕ, 2 ≤ x →
      c₁ / log x ≤ primeProduct x ∧ primeProduct x ≤ c₂ / log x := by
  obtain ⟨B₁, C₁, hM⟩ := mertens_second_theorem
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1 : 0 ≤ C₁ := by
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  -- Convergence of Σ_{n ≥ 1} 1/n² bounds the prime subsum of 2/p².
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)
  have hbound : ∃ T : ℝ, 0 ≤ T ∧
      ∀ s : Finset ℕ, s.sum (fun p => 2 / (p : ℝ) ^ 2) ≤ T := by
    refine ⟨2 * ∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ), ?_, ?_⟩
    · exact mul_nonneg (by norm_num) (tsum_nonneg (fun n => by positivity))
    · intro s
      calc
        s.sum (fun p => 2 / (p : ℝ) ^ 2) = 2 * s.sum (fun p => 1 / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          congr 1
          ext p
          ring
        _ ≤ 2 * (∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (Summable.sum_le_tsum s (fun n _hn => by positivity) hsum2) (by norm_num)
  obtain ⟨T, hT0, hbound⟩ := hbound
  -- Local logarithmic correction at each prime.
  have hlocal : ∀ p : ℕ, p.Prime →
      |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 :=
    by
    intro p hp
    exact log_one_sub_prime_bound hp
  refine ⟨exp (-B₁ - T - C₁ / log 2), exp (-B₁ + T + C₁ / log 2), ?_, ?_⟩
  · exact Real.exp_pos _
  · intro x hx
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    have hlogxpos : 0 < log x := Real.log_pos hx1
    have hprod_pos : 0 < primeProduct x := by
      unfold primeProduct
      exact Finset.prod_pos (fun p hp => by
        have hp' : p.Prime := (mem_filter.mp hp).2
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
        have hdiv : 1 / (p : ℝ) < 1 := by
          rw [div_lt_iff₀ (by positivity : 0 < (p : ℝ))]
          nlinarith
        linarith)
    -- log Π = Σ log(1 - 1/p)
    have hlogprod : log (primeProduct x) =
        ((range (x + 1)).filter Nat.Prime).sum (fun p => log (1 - 1 / (p : ℝ))) := by
      unfold primeProduct
      rw [Real.log_prod]
      intro p hp
      have hp' : p.Prime := (mem_filter.mp hp).2
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
      have hdiv : 1 / (p : ℝ) < 1 := by
        rw [div_lt_iff₀ (by positivity : 0 < (p : ℝ))]
        nlinarith
      linarith
    -- E(x) := Σ_{p ≤ x} (-log(1-1/p) - 1/p), |E(x)| ≤ T
    let E : ℝ := ((range (x + 1)).filter Nat.Prime).sum
      (fun p => -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))
    have hneglog : -log (primeProduct x) = primeReciprocalSum x + E := by
      unfold E primeReciprocalSum
      rw [hlogprod]
      rw [← Finset.sum_neg_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    have hEabs : |E| ≤ T := by
      unfold E
      calc
        |((range (x + 1)).filter Nat.Prime).sum
            (fun p => -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))|
            ≤ ((range (x + 1)).filter Nat.Prime).sum
              (fun p => |(-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))|) :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ((range (x + 1)).filter Nat.Prime).sum (fun p => 2 / (p : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' : p.Prime := (mem_filter.mp hp).2
            have h := hlocal p hp'
            rw [← abs_neg] at h
            rwa [show (-(log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) =
                -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) by ring] at h
        _ ≤ T := hbound _
    -- δ := S(x) - (log log x + B₁), |δ| ≤ C₁/log x
    let δ : ℝ := primeReciprocalSum x - (log (log x) + B₁)
    have hδ_le : |δ| ≤ C₁ / log x := by
      simpa [δ] using (hM x hx)
    have hδ_le2 : |δ| ≤ C₁ / log 2 := by
      have hlelog : log 2 ≤ log x :=
        (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < x))).2 (by exact_mod_cast hx)
      exact le_trans hδ_le (div_le_div_of_nonneg_left hC1 hlog2 hlelog)
    -- Π = exp(-B₁ - δ - E) / log x
    have hlogP : log (primeProduct x) = -(log (log x) + B₁ + δ + E) := by
      have h1 : -log (primeProduct x) = log (log x) + B₁ + δ + E := by
        rw [hneglog]
        unfold δ
        ring
      linarith
    have hP' : primeProduct x = exp (-B₁ - δ - E) / log x := by
      rw [← Real.exp_log hprod_pos]
      have hsplit : -(log (log x) + B₁ + δ + E) = -log (log x) + (-B₁ - δ - E) := by ring
      rw [hlogP, hsplit, Real.exp_add, Real.exp_neg, Real.exp_log (by positivity : 0 < log x)]
      rw [div_eq_mul_inv]
      ring
    -- Bounds: exp(-B₁ - T - C₁/log2) ≤ exp(-B₁-δ-E) ≤ exp(-B₁ + T + C₁/log2).
    have hlower : -B₁ - T - C₁ / log 2 ≤ -B₁ - δ - E := by
      have hδ : δ ≤ |δ| := le_abs_self _
      have hE : E ≤ |E| := le_abs_self _
      nlinarith [hδ, hE, hδ_le2, hEabs, hT0]
    have hupper : -B₁ - δ - E ≤ -B₁ + T + C₁ / log 2 := by
      have hδ' : -δ ≤ |δ| := neg_le_abs δ
      have hE' : -E ≤ |E| := neg_le_abs E
      nlinarith [hδ', hE', hδ_le2, hEabs, hT0]
    have hP_low : exp (-B₁ - T - C₁ / log 2) ≤ exp (-B₁ - δ - E) :=
      Real.exp_le_exp.mpr hlower
    have hP_up : exp (-B₁ - δ - E) ≤ exp (-B₁ + T + C₁ / log 2) :=
      Real.exp_le_exp.mpr hupper
    rw [hP']
    constructor
    · exact div_le_div_of_nonneg_right hP_low (le_of_lt hlogxpos)
    · exact div_le_div_of_nonneg_right hP_up (le_of_lt hlogxpos)

/-! ## 3. Application: bounded prime-reciprocal sums (Lemma 1) -/

/-- `primeReciprocalSum` is monotone: x ≤ y ⟹ Σ_{p ≤ x} 1/p ≤ Σ_{p ≤ y} 1/p. -/
private lemma primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro a b hab
  unfold primeReciprocalSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hfn
  · intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p _hp _hnot
    exact div_nonneg zero_le_one (by positivity)

/-- S(u) = 0 for u ≤ 1, since no prime is at most 1. -/
private lemma primeReciprocalSum_zero_of_le_one {u : ℕ} (hu : u ≤ 1) :
    primeReciprocalSum u = 0 := by
  unfold primeReciprocalSum
  interval_cases u
  · rw [Finset.sum_filter]
    norm_num [Finset.sum_range_succ]
  · rw [Finset.sum_filter]
    norm_num [Finset.sum_range_succ, Nat.not_prime_one]

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
  obtain ⟨_B₁, C₁, hM⟩ := mertens_second_theorem
  -- C₁ ≥ 0 follows from the bound at x = 2.
  have hC1 : 0 ≤ C₁ := by
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  -- x₀ bounds x when x^α < 2; K is the maximum of log(2/α) and 0.
  let x₀ : ℕ := ⌊(2 : ℝ) ^ (1 / α)⌋₊
  let K : ℝ := max (log (2 / α)) 0
  refine ⟨max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2), ?_⟩
  intro x hx
  let T : Finset ℕ := (range (x + 1)).filter (fun p => Nat.Prime p ∧
    ((x : ℝ) ^ α < (p : ℝ) ∧ (p : ℝ) ≤ (x : ℝ) ^ β))
  let U : Finset ℕ := (range (x + 1)).filter (fun p => Nat.Prime p ∧
    (x : ℝ) ^ α < (p : ℝ))
  let u : ℕ := ⌊(x : ℝ) ^ α⌋₊
  have hxα0 : 0 ≤ (x : ℝ) ^ α :=
    Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ x)) α
  -- T ⊆ U: drop the condition p ≤ x^β while retaining the common cutoff p ≤ x.
  have hTsub : T ⊆ U := by
    intro p hp
    simp only [T, U, mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hTnonneg : 0 ≤ T.sum (fun p => 1 / (p : ℝ)) := by
    exact Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (by positivity))
  -- Main estimate: the sum over U is at most max (S x₀) (K + 2C₁/log 2).
  have hUbound : U.sum (fun p => 1 / (p : ℝ)) ≤
      max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) := by
    by_cases hux : u ≤ x
    · -- U = {primes p ≤ x} \ {primes p ≤ u}, so U.sum = S x - S u.
      have hUeq : U.sum (fun p => 1 / (p : ℝ)) =
          primeReciprocalSum x - primeReciprocalSum u := by
        have hsub2 : (range (u + 1)).filter Nat.Prime ⊆
            (range (x + 1)).filter Nat.Prime := by
          intro p hp
          simp only [mem_filter, mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
        have hUsdiff : U = (range (x + 1)).filter Nat.Prime \
            (range (u + 1)).filter Nat.Prime := by
          ext p
          simp only [U, mem_filter, Finset.mem_sdiff, mem_range]
          constructor
          · rintro ⟨hpx, hpP, hxp⟩
            refine ⟨⟨hpx, hpP⟩, ?_⟩
            intro hpu
            have hu_lt_p' : ⌊(x : ℝ) ^ α⌋₊ < p := (Nat.floor_lt hxα0).mpr hxp
            have hu_lt_p : u < p := by
              simpa [u] using hu_lt_p'
            omega
          · rintro ⟨⟨hpx, hpP⟩, hnot⟩
            refine ⟨hpx, hpP, ?_⟩
            have hup : u < p := by
              by_contra h
              have hp_le_u : p ≤ u := le_of_not_gt h
              have hp_lt_u1 : p < u + 1 := by omega
              exact hnot ⟨hp_lt_u1, hpP⟩
            have hup' : ⌊(x : ℝ) ^ α⌋₊ < p := by simpa [u] using hup
            exact (Nat.floor_lt hxα0).mp hup'
        rw [hUsdiff]
        exact eq_sub_of_add_eq (Finset.sum_sdiff (s₁ := (range (u + 1)).filter Nat.Prime)
          (s₂ := (range (x + 1)).filter Nat.Prime) hsub2)
      by_cases hu2 : 2 ≤ u
      · -- Main case: subtract the two Mertens bounds.
        have hlogxpos : 0 < log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
        have hlogupos : 0 < log u := Real.log_pos (by exact_mod_cast (by omega : 1 < u))
        have hlog2pos : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have hMx := hM x hx
        have hMu := hM u hu2
        have hLx : primeReciprocalSum x - (log (log x) + _B₁) ≤ C₁ / log x :=
          (abs_le.mp hMx).2
        have hLu : (log (log u) + _B₁) - primeReciprocalSum u ≤ C₁ / log u := by
          have h := (abs_le.mp hMu).1
          linarith
        -- log x / log u ≤ 2 / α
        have hlogratio : log x / log u ≤ 2 / α := by
          have hα0 : α ≠ 0 := ne_of_gt hα
          by_cases hbig : (2 * log 2 / α) ≤ log x
          · -- log u ≥ α·log x - log 2 ≥ (α/2)·log x
            have hcross : 2 * log 2 ≤ α * log x := by
              have := (div_le_iff₀ hα).mp hbig
              nlinarith
            have hden : 0 < α * log x - log 2 := by
              nlinarith [hcross, hlog2pos]
            have hxα2 : (2 : ℝ) ≤ (x : ℝ) ^ α := by
              have hu_le : (u : ℝ) ≤ (x : ℝ) ^ α := Nat.floor_le hxα0
              have hu2' : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
              nlinarith
            have hfl : (x : ℝ) ^ α / 2 ≤ u := by
              have hlt := Nat.lt_floor_add_one (a := (x : ℝ) ^ α)
              nlinarith [hlt, hxα2]
            have hlogu_ge : α * log x - log 2 ≤ log u := by
              have hpos1 : 0 < (x : ℝ) ^ α / 2 := by positivity
              have hpos2 : 0 < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
              calc
                α * log x - log 2 = log ((x : ℝ) ^ α / 2) := by
                  rw [Real.log_div (by positivity : (x : ℝ) ^ α ≠ 0)
                    (by norm_num : (2 : ℝ) ≠ 0)]
                  rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < x))]
              _ ≤ log u := (Real.log_le_log_iff hpos1 hpos2).2 hfl
            have hfrac : log x / (α * log x - log 2) ≤ 2 / α := by
              rw [div_le_iff₀ hden]
              field_simp [hα0, hden.ne']
              nlinarith [hcross]
            calc
              log x / log u ≤ log x / (α * log x - log 2) :=
                div_le_div_of_nonneg_left (le_of_lt hlogxpos) hden hlogu_ge
              _ ≤ 2 / α := hfrac
          · -- log x < 2·log 2/α: log x/log u ≤ log x/log 2 ≤ 2/α
            have hlt : log x < 2 * log 2 / α := lt_of_not_ge hbig
            have hle1 : log x / log u ≤ log x / log 2 := by
              have hlog2_le_logu : log 2 ≤ log u :=
                (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
                  (by exact_mod_cast (by omega : 0 < u))).2 (by exact_mod_cast hu2)
              exact div_le_div_of_nonneg_left (le_of_lt hlogxpos) hlog2pos hlog2_le_logu
            have hcross2 : α * log x < 2 * log 2 := by
              have := (lt_div_iff₀ hα).mp hlt
              nlinarith
            have hle2 : log x / log 2 ≤ 2 / α := by
              rw [div_le_iff₀ hlog2pos]
              field_simp [hα0]
              nlinarith [hcross2]
            exact hle1.trans hle2
        -- log(log x) - log(log u) = log(log x / log u) ≤ log(2/α)
        have hLdiff : log (log x) - log (log u) ≤ log (2 / α) := by
          have hdivpos : 0 < log x / log u := div_pos hlogxpos hlogupos
          have h2a : 0 < 2 / α := div_pos (by norm_num) hα
          calc
            log (log x) - log (log u) = log (log x / log u) := by
              rw [← Real.log_div (ne_of_gt hlogxpos) (ne_of_gt hlogupos)]
          _ ≤ log (2 / α) := (Real.log_le_log_iff hdivpos h2a).2 hlogratio
        -- Combine the difference estimates.
        have hdiff : primeReciprocalSum x - primeReciprocalSum u ≤
            (log (log x) - log (log u)) + C₁ / log x + C₁ / log u := by
          nlinarith [hLx, hLu]
        have hlelog : log 2 ≤ log x :=
          (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
            (by exact_mod_cast (by omega : 0 < x))).2 (by exact_mod_cast hx)
        have hlelogu : log 2 ≤ log u :=
          (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
            (by exact_mod_cast (by omega : 0 < u))).2 (by exact_mod_cast hu2)
        have hc1x : C₁ / log x ≤ C₁ / log 2 :=
          div_le_div_of_nonneg_left hC1 hlog2pos hlelog
        have hc1u : C₁ / log u ≤ C₁ / log 2 :=
          div_le_div_of_nonneg_left hC1 hlog2pos hlelogu
        have hK1 : log (2 / α) ≤ K := by
          unfold K
          exact le_max_left _ _
        have h2div : 2 * C₁ / log 2 = C₁ / log 2 + C₁ / log 2 := by
          field_simp [hlog2pos.ne']
          ring
        have hfinal : primeReciprocalSum x - primeReciprocalSum u ≤ K + 2 * C₁ / log 2 := by
          calc
            primeReciprocalSum x - primeReciprocalSum u
                ≤ (log (log x) - log (log u)) + C₁ / log x + C₁ / log u := hdiff
            _ ≤ log (2 / α) + C₁ / log 2 + C₁ / log 2 := by
                nlinarith [hLdiff, hc1x, hc1u]
            _ ≤ K + 2 * C₁ / log 2 := by
                rw [h2div]
                nlinarith [hK1]
        rw [hUeq]
        exact hfinal.trans (le_max_right _ _)
      · -- u ≤ 1: x is bounded, and S x ≤ S x₀.
        have hu1 : u ≤ 1 := by omega
        have hUzero : primeReciprocalSum u = 0 := primeReciprocalSum_zero_of_le_one hu1
        have hxlt : (x : ℝ) < (2 : ℝ) ^ (1 / α) := by
          have hu2' : u < 2 := by omega
          have hxαlt2 : (x : ℝ) ^ α < 2 := by
            simpa [u] using (Nat.floor_lt hxα0).mp hu2'
          have hxpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
          have hpow := Real.rpow_lt_rpow hxα0 hxαlt2 (by positivity : 0 < 1 / α)
          have hα0 : α ≠ 0 := ne_of_gt hα
          have hmul : ((x : ℝ) ^ α) ^ (1 / α) = (x : ℝ) := by
            rw [← Real.rpow_mul (le_of_lt hxpos)]
            have hαmul : α * (1 / α) = 1 := by
              field_simp [hα0]
            rw [hαmul, Real.rpow_one]
          rwa [hmul] at hpow
        have hxle0 : x ≤ x₀ := by
          have hxle : (x : ℝ) ≤ (2 : ℝ) ^ (1 / α) := le_of_lt hxlt
          exact (Nat.le_floor_iff (by positivity : 0 ≤ (2 : ℝ) ^ (1 / α))).2 hxle
        have hSx : primeReciprocalSum x ≤ primeReciprocalSum x₀ :=
          primeReciprocalSum_mono hxle0
        have hS0 : primeReciprocalSum x₀ ≤
            max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) :=
          le_max_left _ _
        rw [hUeq, hUzero, sub_zero]
        exact hSx.trans hS0
    · -- u > x: U is empty.
      have hxltu : x < u := lt_of_not_ge hux
      have hUempty : U.sum (fun p => 1 / (p : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp only [U, mem_filter, mem_range] at hp
        obtain ⟨hpx, _hp, hxp⟩ := hp
        have hp_lt_u : p < u := by omega
        have hu_lt_p' : ⌊(x : ℝ) ^ α⌋₊ < p := (Nat.floor_lt hxα0).mpr hxp
        have hu_lt_p : u < p := by
          simpa [u] using hu_lt_p'
        omega
      have hCnonneg : 0 ≤ max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) := by
        have hSx0 : 0 ≤ primeReciprocalSum x₀ := by
          unfold primeReciprocalSum
          exact Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (by positivity))
        exact le_max_of_le_left hSx0
      rw [hUempty]
      exact hCnonneg
  -- Combine: |T.sum| = T.sum ≤ U.sum ≤ C.
  calc
    |T.sum (fun p => 1 / (p : ℝ))| = T.sum (fun p => 1 / (p : ℝ)) := abs_of_nonneg hTnonneg
    _ ≤ U.sum (fun p => 1 / (p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub
        (fun p _hp _hnot => div_nonneg zero_le_one (by positivity))
    _ ≤ max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) := hUbound

/-! ## 4. Application: an asymptotic formula for the sieve product V(z) -/

/-- Goldbach sieve product V(z, N) = Π_{p < z, p ∤ N} (1 - 1/(p-1)). -/
noncomputable def goldbachSieveProduct (N z : ℕ) : ℝ :=
  ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1))

/-- Local logarithmic correction for an odd prime p ≥ 3:
|log(1 - 1/(p-1)) + 1/(p-1)| ≤ 2/(p-1)². -/
private lemma log_one_sub_prime_odd_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    |log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1)| ≤ 2 / ((p : ℝ) - 1) ^ 2 := by
  let t : ℝ := 1 / ((p : ℝ) - 1)
  have hp3 : 3 ≤ p := by
    have h2lt : 2 < p := by
      have h2le : 2 ≤ p := hp.two_le
      omega
    omega
  have ht0 : 0 < t := by
    unfold t
    have hpos : 0 < (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    exact div_pos one_pos hpos
  have htle : t ≤ 1 / 2 := by
    unfold t
    have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have : 0 < (p : ℝ) - 1 := by linarith
    exact ne_of_gt this
  have hsubst : |log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1)| =
      |log (1 - t) + t| := by
    simp [t]
  have hrhs : 2 * t ^ 2 = 2 / ((p : ℝ) - 1) ^ 2 := by
    unfold t
    field_simp [hp1]
  rw [hsubst, ← hrhs]
  exact log_one_sub_bound ht0 htle

/-- **Sieve-product lower bound**: there is c₁ > 0 such that, for every
even N ≥ 4 and z ≥ 2,
  c₁ / log z ≤ V(z, N) = Π_{p < z, p ∤ N}(1 - 1/(p-1)).

Proof outline:
  1. Evenness of N excludes p = 2 from the sieve product. Omitting factors
     with p | N can only increase the product, so
     V ≥ W(z) := Π_{p < z, p > 2}(1 - 1/(p-1)).
  2. Use the local correction |log(1 - 1/(p-1)) + 1/(p-1)| ≤ 2/(p-1)².
  3. By Mertens' second theorem,
     -log W = Σ_{p<z,p>2} 1/(p-1) + O(1) ≤ log log z + O(1).
  4. Exponentiating gives W = exp(log W) ≥ e^{-C}/log z.

This supplies the lower-bound scale in V ≈ 𝔖(N)·e^{-γ}/log z,
as needed for the Jurkat-Richert main term. -/
theorem goldbachSieveProduct_lower_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ N z : ℕ, 2 ≤ z → Even N → 4 ≤ N →
      c₁ / log z ≤ goldbachSieveProduct N z := by
  obtain ⟨B₁, C₁, hM⟩ := mertens_second_theorem
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1 : 0 ≤ C₁ := by
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  -- The sums of 1/p² over primes are bounded.
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)
  have hK : ∃ K : ℝ, 0 ≤ K ∧
      ∀ z : ℕ, ((range z).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) ≤ K := by
    refine ⟨∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ), tsum_nonneg (fun n => by positivity), ?_⟩
    intro z
    exact Summable.sum_le_tsum ((range z).filter Nat.Prime)
      (fun n _hn => by positivity) hsum2
  obtain ⟨K, hK0, hK⟩ := hK
  let Ctotal : ℝ := B₁ + C₁ / log 2 + 12 * K
  refine ⟨exp (-Ctotal), by exact Real.exp_pos _, ?_⟩
  intro N z hz hN hN4
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hlogzpos : 0 < log z := Real.log_pos hz1
  let W : ℝ := ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1))
  -- V ≥ W: the sifting set for V is contained in that for W, and factors lie in (0, 1].
  have hVsub : ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)) ⊆
      ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    rcases hp with ⟨hpz, hpP, hpndvd⟩
    have hpne2 : p ≠ 2 := by
      intro hp2
      have h2dvd : 2 ∣ N := by
        rcases hN with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        rw [hk]
        omega
      exact hpndvd (by simpa [hp2] using h2dvd)
    exact ⟨hpz, hpP, hpne2⟩
  have hVgeW : W ≤ goldbachSieveProduct N z := by
    unfold W goldbachSieveProduct
    refine Finset.prod_le_prod_of_subset_of_le_one hVsub ?_ ?_
    · intro p hp
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
      have hp3 : 3 ≤ p := by
        have h2lt : 2 < p := by
          have h2le : 2 ≤ p := hp'.two_le
          omega
        omega
      -- 0 ≤ 1 - 1/(p-1)
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
        have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
      linarith
    · intro p hp _hnot
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
      have hp3 : 3 ≤ p := by
        have h2lt : 2 < p := by
          have h2le : 2 ≤ p := hp'.two_le
          omega
        omega
      have hpos : 0 < (p : ℝ) - 1 := by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
        div_nonneg zero_le_one (le_of_lt hpos)
      exact sub_le_self (a := (1 : ℝ)) hnonneg
  -- log W = Σ log(1 - 1/(p-1))
  have hlogW : log W = ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
      (fun p => log (1 - 1 / ((p : ℝ) - 1))) := by
    unfold W
    rw [Real.log_prod]
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2.1
    have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
    have hp3 : 3 ≤ p := by
      have h2lt : 2 < p := by
        have h2le : 2 ≤ p := hp'.two_le
        omega
      omega
    have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
      have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
    have hlt : 1 / ((p : ℝ) - 1) < 1 := by
      have h12 : (1 / 2 : ℝ) < 1 := by norm_num
      exact lt_of_le_of_lt hle h12
    have hfac : (1 - 1 / ((p : ℝ) - 1)) ≠ 0 := by linarith
    exact hfac
  -- E(z) := Σ_{p<z,p>2} (-log(1-1/(p-1)) - 1/(p-1)), |E| ≤ 8K
  let E : ℝ := ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
    (fun p => -log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1))
  have hneglog : -log W =
      ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
        (fun p => 1 / ((p : ℝ) - 1)) + E := by
    unfold E
    rw [hlogW]
    rw [← Finset.sum_neg_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hEabs : |E| ≤ 8 * K := by
    unfold E
    calc
      |((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
          (fun p => -log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1))|
          ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => |(-log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1))|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => 2 / ((p : ℝ) - 1) ^ 2) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' : p.Prime := (mem_filter.mp hp).2.1
          have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
          have h := log_one_sub_prime_odd_bound hp' hp2
          rw [← abs_neg] at h
          rwa [show (-(log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1))) =
              -log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1) by ring] at h
      _ ≤ ((range z).filter Nat.Prime).sum (fun p => 8 / (p : ℝ) ^ 2) := by
          calc
            ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                (fun p => 2 / ((p : ℝ) - 1) ^ 2)
              ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                  (fun p => 8 / (p : ℝ) ^ 2) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  have hp' : p.Prime := (mem_filter.mp hp).2.1
                  have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
                  have hp3 : 3 ≤ p := by
                    have h2lt : 2 < p := by
                      have h2le : 2 ≤ p := hp'.two_le
                      omega
                    omega
                  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
                  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
                    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                    have : 0 < (p : ℝ) - 1 := by linarith
                    exact ne_of_gt this
                  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
                  have hpos1 : 0 < (p : ℝ) - 1 := by
                    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                    linarith
                  have hpos2 : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos (by linarith : 0 < (p : ℝ))
                  rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) hpos2]
                  nlinarith
            _ ≤ ((range z).filter Nat.Prime).sum (fun p => 8 / (p : ℝ) ^ 2) := by
                  exact Finset.sum_le_sum_of_subset_of_nonneg
                    (by
                      intro p hp
                      simp only [mem_filter, mem_range] at hp ⊢
                      exact ⟨by omega, hp.2.1⟩)
                    (fun p _hp _hnot => by positivity)
      _ ≤ 8 * K := by
          calc
            ((range z).filter Nat.Prime).sum (fun p => 8 / (p : ℝ) ^ 2)
                = 8 * ((range z).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) := by
                  rw [Finset.mul_sum]
                  congr 1
                  ext p
                  ring
            _ ≤ 8 * K := mul_le_mul_of_nonneg_left (hK z) (by norm_num)
  -- Σ_{p<z,p>2} 1/(p-1) ≤ S(z) + 4K
  have hsum_le : ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
      (fun p => 1 / ((p : ℝ) - 1)) ≤ primeReciprocalSum z + 4 * K := by
    calc
      ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
          (fun p => 1 / ((p : ℝ) - 1))
          ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
              (fun p => 1 / (p : ℝ) + 1 / ((p : ℝ) - 1) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' : p.Prime := (mem_filter.mp hp).2.1
            have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
            have hp3 : 3 ≤ p := by
              have h2lt : 2 < p := by
                have h2le : 2 ≤ p := hp'.two_le
                omega
              omega
            -- 1/(p-1) = 1/p + 1/(p(p-1)) ≤ 1/p + 1/(p-1)²
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
            have hpm1 : (p : ℝ) - 1 ≠ 0 := by
              have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
              have : 0 < (p : ℝ) - 1 := by linarith
              exact ne_of_gt this
            have hle : 1 / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) + 1 / ((p : ℝ) - 1) ^ 2 := by
              -- 1/(p-1) - 1/(p-1)² = (p-2)/(p-1)² ≤ 1/p
              have hpos1 : 0 < (p : ℝ) - 1 := by
                have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                linarith
              have hpos2 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
              have hstep : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 =
                  ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
                field_simp [hpm1]
                ring
              have hle' : ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
                rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) hpos2]
                nlinarith
              have hsub : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
                rwa [hstep]
              nlinarith
            exact hle
      _ = ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => 1 / (p : ℝ)) +
          ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => 1 / ((p : ℝ) - 1) ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ ≤ primeReciprocalSum z + 4 * K := by
          -- Σ_{p<z,p>2} 1/p ≤ S(z); Σ_{p<z,p>2} 1/(p-1)² ≤ 4K
          have h1 : ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
              (fun p => 1 / (p : ℝ)) ≤ primeReciprocalSum z := by
            unfold primeReciprocalSum
            -- Compare the sum over a subset.
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro p hp; simp only [mem_filter, mem_range] at hp ⊢; exact ⟨by omega, hp.2.1⟩)
              (fun p _hp _hnot => by positivity)
          have h2 : ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
              (fun p => 1 / ((p : ℝ) - 1) ^ 2) ≤ 4 * K := by
            calc
              ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                  (fun p => 1 / ((p : ℝ) - 1) ^ 2)
                  ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                      (fun p => 4 / (p : ℝ) ^ 2) := by
                    apply Finset.sum_le_sum
                    intro p hp
                    have hp' : p.Prime := (mem_filter.mp hp).2.1
                    have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
                    have hp3 : 3 ≤ p := by
                      have h2lt : 2 < p := by
                        have h2le : 2 ≤ p := hp'.two_le
                        omega
                      omega
                    have hpos1 : 0 < (p : ℝ) - 1 := by
                      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                      linarith
                    have hpos2 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
                    rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) (sq_pos_of_pos hpos2)]
                    have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
                    nlinarith
              _ ≤ ((range z).filter Nat.Prime).sum (fun p => 4 / (p : ℝ) ^ 2) := by
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (by
                        intro p hp
                        simp only [mem_filter, mem_range] at hp ⊢
                        exact ⟨by omega, hp.2.1⟩)
                      (fun p _hp _hnot => by positivity)
              _ = 4 * ((range z).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) := by
                    rw [Finset.mul_sum]
                    congr 1
                    ext p
                    ring
              _ ≤ 4 * K := mul_le_mul_of_nonneg_left (hK z) (by norm_num)
          nlinarith
  -- -log W ≤ log log z + Ctotal
  have hS : primeReciprocalSum z ≤ log (log z) + B₁ + C₁ / log 2 := by
    have hMz := hM z hz
    have h1 : primeReciprocalSum z ≤ log (log z) + B₁ + C₁ / log z := by
      have h := (abs_le.mp hMz).2
      linarith
    have h2 : C₁ / log z ≤ C₁ / log 2 := by
      have hlelog : log 2 ≤ log z :=
        (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < z))).2 (by exact_mod_cast hz)
      exact div_le_div_of_nonneg_left hC1 hlog2 hlelog
    nlinarith
  have hneg_le : -log W ≤ log (log z) + Ctotal := by
    have hE : E ≤ |E| := le_abs_self _
    have h1 : -log W ≤ (primeReciprocalSum z + 4 * K) + 8 * K := by
      nlinarith [hneglog, hE, hEabs, hsum_le]
    unfold Ctotal
    nlinarith [h1, hS]
  -- W ≥ e^{-Ctotal}/log z
  have hWpos : 0 < W := by
    unfold W
    exact Finset.prod_pos (fun p hp => by
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
      have hp3 : 3 ≤ p := by
        have h2lt : 2 < p := by
          have h2le : 2 ≤ p := hp'.two_le
          omega
        omega
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
        have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
      have hlt : 1 / ((p : ℝ) - 1) < 1 := by
        have h12 : (1 / 2 : ℝ) < 1 := by norm_num
        exact lt_of_le_of_lt hle h12
      linarith)
  have hW_low : exp (-Ctotal) / log z ≤ W := by
    have hlogW_ge : -log (log z) - Ctotal ≤ log W := by linarith [hneg_le]
    have h1 : exp (-log (log z) - Ctotal) ≤ exp (log W) :=
      Real.exp_le_exp.mpr hlogW_ge
    have hWexp : exp (log W) = W := Real.exp_log hWpos
    have h2 : exp (-log (log z) - Ctotal) = exp (-Ctotal) / log z := by
      rw [show -log (log z) - Ctotal = -log (log z) + (-Ctotal) by ring, Real.exp_add]
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < log z)]
      rw [div_eq_mul_inv]
      ring
    rw [hWexp] at h1
    rwa [h2] at h1
  exact hW_low.trans hVgeW

/-- Sieve-product upper bound: V(z, N) ≤ 1, since every factor lies in [0, 1].
The factor at p = 2 can be zero when N is odd. -/
theorem goldbachSieveProduct_le_one (N z : ℕ) :
    goldbachSieveProduct N z ≤ 1 := by
  unfold goldbachSieveProduct
  exact Finset.prod_le_one
    (fun (p : ℕ) hp => by
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : 2 ≤ p := hp'.two_le
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
        have hpos : 0 < (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        rw [div_le_iff₀ hpos]
        have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        nlinarith
      linarith)
    (fun (p : ℕ) hp => by
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : 2 ≤ p := hp'.two_le
      have hpos : 0 < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
        div_nonneg zero_le_one (le_of_lt hpos)
      exact sub_le_self (a := (1 : ℝ)) hnonneg)

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
  rw [hrangeP]
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
    unfold SingularSeries.localFactor
    rw [if_neg hpne2, if_neg hpnd]
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
    unfold SingularSeries.localFactor
    by_cases hp2 : p = 2
    · subst hp2
      rw [if_pos rfl, if_pos h2dvd]
      norm_num
    · rw [if_neg hp2, if_pos hpd]
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

/-- **Order of the sieve product**: there are c₁, c₂ > 0 such that,
for every even N ≥ 4 and z ≥ 3,
  c₁·𝔖(N,z-1)/log z ≤ V(z,N) ≤ c₂·𝔖(N,z-1)/log z.

This follows directly from V = Π_{p<z}(1-1/p)·𝔖(N,z-1) and
`primeProduct_asymptotic_order`, which gives Π_{p<z}(1-1/p) = Θ(1/log z). -/
theorem sieveProduct_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ N z : ℕ, 3 ≤ z → Even N → 4 ≤ N →
      c₁ * SingularSeries.singularSeriesTruncated N (z - 1) / log z ≤
        goldbachSieveProduct N z ∧
      goldbachSieveProduct N z ≤
        c₂ * SingularSeries.singularSeriesTruncated N (z - 1) / log z := by
  obtain ⟨c₁0, c₂0, hc₁0, hPP⟩ := primeProduct_asymptotic_order
  refine ⟨c₁0, 2 * c₂0, hc₁0, ?_⟩
  intro N z hz hN hN4
  have h1z : 1 ≤ z := by omega
  have hz2 : 2 ≤ z - 1 := by omega
  have hz1 : 1 ≤ z - 1 := by omega
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast (by omega : 3 ≤ z)
  have hlogz : 0 < log z := Real.log_pos (by linarith : (1 : ℝ) < z)
  have hz1r : (1 : ℝ) < (z : ℝ) - 1 := by linarith
  have hcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 :=
    by simpa using (Nat.cast_sub h1z)
  have hlogz1 : 0 < log (z - 1) := by
    exact Real.log_pos hz1r
  have h𝔖 : 0 < SingularSeries.singularSeriesTruncated N (z - 1) :=
    SingularSeries.singularSeriesTruncated_pos N (z - 1) hz1
  have hP := hPP (z - 1) hz2
  have hlelog1 : log (z - 1) ≤ log z := by
    have hpos1 : 0 < (z : ℝ) - 1 := by linarith
    have hle1 : (z : ℝ) - 1 ≤ (z : ℝ) := by linarith
    exact (Real.log_le_log_iff hpos1 (by linarith : 0 < (z : ℝ))).2 hle1
  have hlog_ratio : (1 / 2 : ℝ) * log z ≤ log (z - 1) := by
    have hsqrt : Real.sqrt z ≤ (z : ℝ) - 1 := by
      have hz1pos : 0 ≤ (z : ℝ) - 1 := by linarith
      have hsq : (z : ℝ) ≤ ((z : ℝ) - 1) ^ 2 := by
        have hdiff : ((z : ℝ) - 1) ^ 2 - (z : ℝ) =
            ((z : ℝ) - 2) ^ 2 + ((z : ℝ) - 3) := by ring
        have hnonneg : 0 ≤ ((z : ℝ) - 1) ^ 2 - (z : ℝ) := by
          rw [hdiff]
          have h1 : 0 ≤ ((z : ℝ) - 2) ^ 2 := sq_nonneg _
          have h2 : 0 ≤ (z : ℝ) - 3 := by linarith
          nlinarith
        linarith
      exact (Real.sqrt_le_iff).2 ⟨hz1pos, hsq⟩
    have hlogsqrt : log (Real.sqrt z) = (1 / 2 : ℝ) * log z := by
      rw [Real.log_sqrt (by exact_mod_cast (by omega : 0 ≤ z))]
      ring
    have hle : log (Real.sqrt z) ≤ log (z - 1) := by
      have hpos1 : 0 < Real.sqrt z :=
        Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < z))
      have hpos2 : 0 < (z : ℝ) - 1 := by linarith
      exact (Real.log_le_log_iff hpos1 hpos2).2 hsqrt
    rwa [hlogsqrt] at hle
  have hid := sieveProduct_identity N z (by omega) hN
  have hV_low : c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) ≤
      goldbachSieveProduct N z := by
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_right hP.1 (le_of_lt h𝔖)
    -- Normalize hmul : c₁0/log(z-1) · 𝔖 ≤ P·𝔖.
    simpa [div_eq_mul_inv, hcast, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hV_up : goldbachSieveProduct N z ≤
      c₂0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) := by
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_right hP.2 (le_of_lt h𝔖)
    simpa [div_eq_mul_inv, hcast, mul_assoc, mul_left_comm, mul_comm] using hmul
  -- Replace log(z-1) by log z in the bounds.
  have hA : c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) / log z ≤
      c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) := by
    have hnonneg : 0 ≤ c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) :=
      mul_nonneg (le_of_lt hc₁0) (le_of_lt h𝔖)
    exact div_le_div_of_nonneg_left hnonneg hlogz1 hlelog1
  have hB : c₂0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) ≤
      (2 * c₂0) * SingularSeries.singularSeriesTruncated N (z - 1) / log z := by
    -- 1/log(z-1) ≤ 2/log z
    have hnonneg : 0 ≤ c₂0 * SingularSeries.singularSeriesTruncated N (z - 1) := by
      -- c₂0 ≥ 0 follows from the primeProduct upper bound.
      have hc20 : 0 ≤ c₂0 := by
        have hb := hPP 2 (by norm_num)
        have hle1 : (0 : ℝ) ≤ primeProduct 2 := by
          unfold primeProduct
          have hf : (range 3).filter Nat.Prime = {2} := by
            ext p
            simp only [mem_filter, mem_range, mem_singleton]
            constructor
            · intro hp
              rcases hp with ⟨hp3, hpp⟩
              interval_cases p
              · exact absurd hpp Nat.not_prime_zero
              · exact absurd hpp Nat.not_prime_one
              · rfl
            · intro hp
              subst hp
              simp [Nat.prime_two]
          rw [hf]
          norm_num
        have hle2 : primeProduct 2 ≤ c₂0 / log 2 := hb.2
        have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have : (0 : ℝ) ≤ c₂0 / log 2 := le_trans hle1 hle2
        simpa using (le_div_iff₀ hlog2).mp this
      exact mul_nonneg hc20 (le_of_lt h𝔖)
    -- To get c₂0·𝔖/log(z-1) ≤ 2·c₂0·𝔖/log z, use 1/log(z-1) ≤ 2/log z,
    -- which follows from log z ≤ 2·log(z-1).
    have hdiv : (c₂0 * SingularSeries.singularSeriesTruncated N (z - 1)) / log (z - 1) ≤
        (c₂0 * SingularSeries.singularSeriesTruncated N (z - 1)) / (log z / 2) := by
      have hle : log z / 2 ≤ log (z - 1) := by linarith [hlog_ratio]
      exact div_le_div_of_nonneg_left hnonneg (by linarith : 0 < log z / 2) hle
    have hnorm : (c₂0 * SingularSeries.singularSeriesTruncated N (z - 1)) / (log z / 2) =
        (2 * c₂0) * SingularSeries.singularSeriesTruncated N (z - 1) / log z := by
      field_simp [hlogz.ne']
    exact hdiv.trans (le_of_eq hnorm)
  constructor
  · exact hA.trans hV_low
  · exact hV_up.trans hB

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
  obtain ⟨B₁, C₁, hM⟩ := mertens_second_theorem
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_bound
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1 : 0 ≤ C₁ := by
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  refine ⟨max (B₁ + C₁ / log 2 + 4 * K) 0, le_max_right _ _, ?_⟩
  intro y hy
  have hlogy : 0 < log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- Σ 1/p ≤ log(log y) + B₁ + C₁/log 2
  have hS : primeReciprocalSum y ≤ log (log y) + B₁ + C₁ / log 2 := by
    have hMz := hM y (by omega : 2 ≤ y)
    have h1 : primeReciprocalSum y ≤ log (log y) + B₁ + C₁ / log y := by
      have h := (abs_le.mp hMz).2
      linarith
    have h2 : C₁ / log y ≤ C₁ / log 2 := by
      have hlelog : log 2 ≤ log y :=
        (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < y))).2 (by exact_mod_cast (by omega : 2 ≤ y))
      exact div_le_div_of_nonneg_left hC1 hlog2 hlelog
    nlinarith
  -- Σ 1/(p-1) ≤ Σ(1/p + 1/(p-1)²) ≤ S + 4K
  have hsum : ((range (y + 1)).filter Nat.Prime).sum
      (fun p => 1 / ((p : ℝ) - 1)) ≤ primeReciprocalSum y + 4 * K := by
    calc
      ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1))
          ≤ ((range (y + 1)).filter Nat.Prime).sum
              (fun p => 1 / (p : ℝ) + 1 / ((p : ℝ) - 1) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' : p.Prime := (mem_filter.mp hp).2
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
            have hpm1 : (p : ℝ) - 1 ≠ 0 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
              have : 0 < (p : ℝ) - 1 := by linarith
              exact ne_of_gt this
            have hpos1 : 0 < (p : ℝ) - 1 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
              linarith
            have hpos2 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
            have hstep : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 =
                ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
              field_simp [hpm1]
              ring
            have hle' : ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
              rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) hpos2]
              nlinarith
            have hsub : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
              rwa [hstep]
            nlinarith
      _ = ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ)) +
          ((range (y + 1)).filter Nat.Prime).sum
            (fun p => 1 / ((p : ℝ) - 1) ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ ≤ primeReciprocalSum y + 4 * K := by
          have h1 : ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ)) ≤
              primeReciprocalSum y := by
            unfold primeReciprocalSum
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro p hp; simp only [mem_filter, mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩)
              (fun p _hp _hnot => by positivity)
          have h2 : ((range (y + 1)).filter Nat.Prime).sum
              (fun p => 1 / ((p : ℝ) - 1) ^ 2) ≤ 4 * K := by
            calc
              ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1) ^ 2)
                  ≤ ((range (y + 1)).filter Nat.Prime).sum (fun p => 4 / (p : ℝ) ^ 2) := by
                    apply Finset.sum_le_sum
                    intro p hp
                    have hp' : p.Prime := (mem_filter.mp hp).2
                    have hpos1 : 0 < (p : ℝ) - 1 := by
                      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
                      linarith
                    have hpos2 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
                    rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) (sq_pos_of_pos hpos2)]
                    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
                    nlinarith
              _ = 4 * ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) := by
                    rw [Finset.mul_sum]
                    congr 1
                    ext p
                    ring
              _ ≤ 4 * K := mul_le_mul_of_nonneg_left (hK y) (by norm_num)
          nlinarith
  -- Combine the bounds.
  have hle : ((range (y + 1)).filter Nat.Prime).sum
      (fun p => 1 / ((p : ℝ) - 1)) ≤ log (log y) + (B₁ + C₁ / log 2 + 4 * K) := by
    nlinarith [hS, hsum]
  have hmax : B₁ + C₁ / log 2 + 4 * K ≤ max (B₁ + C₁ / log 2 + 4 * K) 0 :=
    le_max_left _ _
  linarith

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

/-- Prime-counting function π(x) = |{p ≤ x : p prime}|. -/
def primeCount (x : ℕ) : ℕ :=
  ((range (x + 1)).filter Nat.Prime).card

/-- The project's finite prime count agrees definitionally with mathlib's
`Nat.primeCounting`.  This is the normalization needed when importing a PNT
stated using mathlib's standard counting function. -/
theorem primeCount_eq_primeCounting (x : ℕ) :
    primeCount x = Nat.primeCounting x := by
  simp only [primeCount, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- A prime-counting PNT in the normal form exported by PNTAnd's `pi_alt`.

This is kept as a separate interface: adapting an external proof to the
project toolchain only has to establish this proposition. -/
def PrimeCountingPNT : Prop :=
  ∃ c : ℕ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℕ, (primeCount x : ℝ) = (1 + c x) * (x : ℝ) / log x

/-- The `pi_alt` normal form implies the epsilon formulation used by the
project's PNT declaration. -/
theorem primeCountingPNT_implies_prime_number_theorem (hPNT : PrimeCountingPNT) :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ,
      ∀ x : ℕ, x₀ ≤ x →
        |(primeCount x : ℝ) - (x : ℝ) / log x| ≤
          ε * (x : ℝ) / log x := by
  obtain ⟨c, hc, hcount⟩ := hPNT
  rw [Asymptotics.isLittleO_iff] at hc
  intro ε hε
  specialize hc (c := ε) hε
  rw [Filter.eventually_atTop] at hc
  obtain ⟨x₀, hx₀⟩ := hc
  refine ⟨max 2 x₀, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hcx : |c x| ≤ ε := by
    have := hx₀ x (le_trans (le_max_right _ _) hx)
    simpa using this
  have hlog : 0 < log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hscale : 0 ≤ (x : ℝ) / log x := by positivity
  rw [hcount x]
  have hrewrite :
      (1 + c x) * (x : ℝ) / log x - (x : ℝ) / log x =
        c x * ((x : ℝ) / log x) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg hscale]
  calc
    |c x| * ((x : ℝ) / log x) ≤ ε * ((x : ℝ) / log x) :=
      mul_le_mul_of_nonneg_right hcx hscale
    _ = ε * (x : ℝ) / log x := by ring

/-- π(x) ≥ 1 for x ≥ 2, since the prime 2 is counted. -/
theorem primeCount_pos (x : ℕ) (hx : 2 ≤ x) : 0 < primeCount x := by
  unfold primeCount
  apply Finset.card_pos.mpr
  use 2
  simp [mem_filter, mem_range, hx, Nat.prime_two]

/-- **Prime number theorem (PNT)**: π(x) ~ x / log x.

That is, |π(x) - x/log x| / (x/log x) → 0 as x → ∞.
The PNT provides one possible route to Mertens' theorems, though elementary
proofs are also available. -/
theorem prime_number_theorem :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ,
      ∀ x : ℕ, x₀ ≤ x →
        |(primeCount x : ℝ) - (x : ℝ) / log x| ≤
          ε * (x : ℝ) / log x := by
  apply primeCountingPNT_implies_prime_number_theorem
  obtain ⟨c, hc, hcount⟩ :=
    AnalyticNumberTheory.PrimeDistribution.natPrimeCountingPNT
  refine ⟨c, hc, ?_⟩
  intro x
  rw [primeCount_eq_primeCounting]
  exact hcount x

/-! ## 6. The twin-prime constant and a finite truncation -/

/-- Legacy finite truncation of the twin-prime Euler product.

This is a working finite product, not the canonical infinite twin-prime
constant, and it is not used to justify the canonical Chen endpoint. -/
noncomputable def twinPrimeConstant : ℝ :=
  -- The true constant is a limit of truncated products, requiring infinite-product convergence.
  -- This finite proxy uses primes < 100; its positivity proof does not depend on that cutoff.
  ((range 100).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The legacy finite twin-prime product is positive because each factor is
positive. -/
theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  -- Each factor 1 - 1/(p-1)² > 0, since p ≥ 3 gives (p-1)² ≥ 4 > 1.
  -- The infinite product also converges, since Σ 1/(p-1)² ≤ 4·Σ 1/p² < ∞;
  -- only positivity of a finite product is used here.
  unfold twinPrimeConstant
  apply Finset.prod_pos
  intro p hp
  simp only [mem_filter, mem_range] at hp
  obtain ⟨_, hp_prime, hp2⟩ := hp
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have h_sq : 1 < (p - 1 : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ p - 1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    nlinarith
  have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
    have h_pos : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1_pos
    rw [div_lt_iff₀ h_pos, one_mul]
    exact h_sq
  linarith

/-- Each factor 1 - 1/(p-1)² < 1: p ≥ 3 gives (p-1)² ≥ 4 > 1,
so 1/(p-1)² > 0. -/
private lemma twinPrimeConstant_factor_lt_one {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    linarith
  have h_sq_pos : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1_pos
  have : 0 < 1 / ((p : ℝ) - 1) ^ 2 := div_pos one_pos h_sq_pos
  linarith

/-- Each factor 1 - 1/(p-1)² ≤ 1. -/
private lemma twinPrimeConstant_factor_le_one {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
  exact le_of_lt (twinPrimeConstant_factor_lt_one hp hp2)

/-- Each factor is positive. -/
private lemma twinPrimeConstant_factor_pos {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    linarith
  have h_sq : 1 < ((p : ℝ) - 1) ^ 2 := by
    have : (2 : ℝ) ≤ p - 1 := by
      have : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
      linarith
    nlinarith
  have h_pos : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1_pos
  have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
    rw [div_lt_iff₀ h_pos, one_mul]
    exact h_sq
  linarith

/-- The finite twin-prime product is less than 1: every factor is in (0, 1),
and the factor at p = 3 is 3/4 < 1. -/
theorem twinPrimeConstant_lt_one : twinPrimeConstant < 1 := by
  -- Separate the factor at p = 3; the product of the remaining factors is at most 1.
  -- product = factor(3) * prod(rest), factor(3) = 3/4, prod(rest) ≤ 1
  -- Thus product ≤ 3/4 < 1.
  unfold twinPrimeConstant
  set S := (range 100).filter (fun p => Nat.Prime p ∧ 2 < p) with hS_def
  -- p = 3 belongs to the set.
  have h_3_mem : 3 ∈ S := by
    rw [hS_def]
    simp [mem_filter, mem_range, Nat.prime_three]
  -- Separate p = 3.
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem h_3_mem]
  -- factor(3) = 3/4
  have h_3_val : 1 - 1 / ((↑3 : ℝ) - 1) ^ 2 = 3 / 4 := by norm_num
  -- The remaining product is at most 1, since all factors lie in (0, 1].
  have h_rest_le : (S \ {3}).prod (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      simp only [Finset.mem_sdiff, mem_singleton] at hp
      obtain ⟨hp_mem, hp_ne⟩ := hp
      simp only [hS_def, mem_filter, mem_range] at hp_mem
      obtain ⟨_, hp_prime, hp2⟩ := hp_mem
      exact le_of_lt (twinPrimeConstant_factor_pos hp_prime hp2)
    · intro p hp
      simp only [Finset.mem_sdiff, mem_singleton] at hp
      obtain ⟨hp_mem, hp_ne⟩ := hp
      simp only [hS_def, mem_filter, mem_range] at hp_mem
      obtain ⟨_, hp_prime, hp2⟩ := hp_mem
      exact twinPrimeConstant_factor_le_one hp_prime hp2
  -- factor(3) ≥ 0
  have h_3_nonneg : 0 ≤ 1 - 1 / ((↑3 : ℝ) - 1) ^ 2 := by linarith [h_3_val]
  -- product ≤ 3/4 * 1 = 3/4 < 1
  have h_prod_le : (1 - 1 / ((↑3 : ℝ) - 1) ^ 2) *
      ((S \ {3}).prod (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2)) ≤ 3 / 4 := by
    calc (1 - 1 / ((↑3 : ℝ) - 1) ^ 2) *
          ((S \ {3}).prod (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2))
        ≤ (1 - 1 / ((↑3 : ℝ) - 1) ^ 2) * 1 := mul_le_mul_of_nonneg_left h_rest_le h_3_nonneg
      _ = 1 - 1 / ((↑3 : ℝ) - 1) ^ 2 := mul_one _
      _ = 3 / 4 := h_3_val
  linarith

/-! ## 6.5 Local interval factors -/

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
  have hlocal := log_one_sub_bound ht htle
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
  obtain ⟨B, C, hM⟩ := mertens_second_theorem
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    have h := hM 2 (by norm_num)
    have : 0 ≤ C / log 2 := le_trans (abs_nonneg _) h
    simpa using (le_div_iff₀ hlog2).mp this
  refine ⟨C, hC, ?_⟩
  intro k n hk hkn s hs
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hlogk : 0 < log k := Real.log_pos hk1
  have hn2 : 2 ≤ n := le_trans hk hkn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < log n := Real.log_pos hn1
  let T := (Finset.Ioo k (n + 1)).filter Nat.Prime
  have hsub : s ⊆ T := by
    intro p hp
    rcases hs p hp with ⟨hpp, hkp, hpn⟩
    simp only [T, Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨hkp, by omega⟩, hpp⟩
  have hprodpos : 0 < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    have hpdata := hs p hp
    have hp3 : 3 ≤ p := by omega
    have hden : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have htwo : (2 : ℝ) ≤ (p : ℝ) - 1 := by
        have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) htwo
      linarith
    exact inv_pos.mpr hden
  have hlogprod :
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
        ∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    rw [Real.log_prod]
    intro p hp
    exact ne_of_gt (inv_pos.mpr (by
      have hpdata := hs p hp
      have hp3 : 3 ≤ p := by omega
      have htwo : (2 : ℝ) ≤ (p : ℝ) - 1 := by
        have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) htwo
      linarith))
  have hlocal :
      (∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
        (∑ p ∈ s, (1 / (p : ℝ) + 12 / (p : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact log_goldbach_inverse_factor_le (hs p hp).1
      (lt_of_le_of_lt hk (hs p hp).2.1)
  have hrecip :
      (∑ p ∈ s, 1 / (p : ℝ)) ≤
        primeReciprocalSum n - primeReciprocalSum k := by
    have hT :
        (∑ p ∈ T, 1 / (p : ℝ)) =
          primeReciprocalSum n - primeReciprocalSum k := by
      let Pn := (Finset.range (n + 1)).filter Nat.Prime
      let Pk := (Finset.range (k + 1)).filter Nat.Prime
      have hPk : Pk ⊆ Pn := by
        intro p hp
        simp only [Pk, Pn, Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by omega, hp.2⟩
      have hTdiff : T = Pn \ Pk := by
        ext p
        simp only [T, Pn, Pk, Finset.mem_filter, Finset.mem_Ioo,
          Finset.mem_sdiff, Finset.mem_range]
        constructor
        · rintro ⟨⟨hkp, hpn⟩, hp⟩
          exact ⟨⟨hpn, hp⟩, by
            intro hpk
            omega⟩
        · rintro ⟨⟨hpn, hp⟩, hnot⟩
          refine ⟨⟨?_, hpn⟩, hp⟩
          by_contra hkp
          apply hnot
          exact ⟨Nat.lt_succ_iff.mpr (le_of_not_gt hkp), hp⟩
      rw [hTdiff, Finset.sum_sdiff_eq_sub hPk]
      rfl
    calc
      (∑ p ∈ s, 1 / (p : ℝ)) ≤ ∑ p ∈ T, 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => div_nonneg zero_le_one (by positivity))
      _ = primeReciprocalSum n - primeReciprocalSum k := hT
  have hMrecip :
      primeReciprocalSum n - primeReciprocalSum k ≤
        log (log n / log k) + 2 * C / log k := by
    have hMn := hM n hn2
    have hMk := hM k hk
    have hupper :
        primeReciprocalSum n ≤ log (log n) + B + C / log n := by
      linarith [(abs_le.mp hMn).2]
    have hlower :
        log (log k) + B - C / log k ≤ primeReciprocalSum k := by
      linarith [(abs_le.mp hMk).1]
    have hCdiv : C / log n ≤ C / log k := by
      apply div_le_div_of_nonneg_left hC hlogk
      exact Real.log_le_log (by positivity) (by exact_mod_cast hkn)
    have hlogs :
        log (log n) - log (log k) = log (log n / log k) := by
      rw [← Real.log_div hlogn.ne' hlogk.ne']
    calc
      primeReciprocalSum n - primeReciprocalSum k ≤
          (log (log n) - log (log k)) + C / log n + C / log k := by
        linarith
      _ ≤ log (log n / log k) + 2 * C / log k := by
        rw [hlogs]
        have htwo : 2 * C / log k = C / log k + C / log k := by ring
        rw [htwo]
        linarith
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
  have hloginv : 1 / (k : ℝ) ≤ 1 / log k := by
    apply one_div_le_one_div_of_le hlogk
    have := Real.log_le_sub_one_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hk) :
      0 < (k : ℝ))
    linarith
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
      have h24 : 24 / (k : ℝ) ≤ 24 / log k := by
        calc
          24 / (k : ℝ) = 24 * (1 / (k : ℝ)) := by ring
          _ ≤ 24 * (1 / log k) :=
            mul_le_mul_of_nonneg_left hloginv (by norm_num)
          _ = 24 / log k := by ring
      have htwentyfour : 12 * (2 / (k : ℝ)) = 24 / (k : ℝ) := by ring
      calc
        (primeReciprocalSum n - primeReciprocalSum k) + 12 * (2 / (k : ℝ)) ≤
            log (log n / log k) + 2 * C / log k + 24 / log k := by
              rw [htwentyfour]
              linarith
        _ = log (log n / log k) + (2 * C + 24) / log k := by ring

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
  let E : ℝ := (D / log 2) * exp (A / log 2)
  let K : ℝ := 2 * D + E * D + 2
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    dsimp [A]
    nlinarith
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  have hDthree : 3 ≤ D := by
    dsimp [D, A]
    nlinarith
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hK : 1 < K := by
    dsimp [K]
    nlinarith
  refine ⟨K, hK, ?_⟩
  intro s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  have hlogz₁ : 0 < log z₁ := Real.log_pos (by linarith)
  have hlogz₁₂ : log z₁ ≤ log z₂ :=
    Real.log_le_log (by linarith) hz₁₂
  have hlogz₂ : 0 < log z₂ := lt_of_lt_of_le hlogz₁ hlogz₁₂
  have hratio_pos : 0 < log z₂ / log z₁ := div_pos hlogz₂ hlogz₁
  have hprodpos : 0 < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : 2 < p := (hs p hp).2
    have hp3 : 3 ≤ p := by omega
    have hden : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have htwo : (2 : ℝ) ≤ (p : ℝ) - 1 := by
        have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) htwo
      linarith
    exact inv_pos.mpr hden
  by_cases hempty : s = ∅
  · subst s
    simp only [Finset.prod_empty]
    have hratio_one : 1 ≤ log z₂ / log z₁ := by
      apply (le_div_iff₀ hlogz₁).mpr
      linarith
    have hfactor_one : 1 ≤ 1 + K / log z₁ := by
      have hKpos : 0 ≤ K := by linarith
      have : 0 ≤ K / log z₁ := div_nonneg hKpos (le_of_lt hlogz₁)
      linarith
    calc
      1 ≤ (log z₂ / log z₁) * 1 := by simpa using hratio_one
      _ ≤ (log z₂ / log z₁) * (1 + K / log z₁) :=
        mul_le_mul_of_nonneg_left hfactor_one (le_of_lt hratio_pos)
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hpz₁ : z₁ ≤ (p : ℝ) := (hsinterval p hp).1
  have hpz₂ : (p : ℝ) < z₂ := (hsinterval p hp).2
  by_cases hlarge : exp D ≤ z₁
  · let k : ℕ := Nat.floor z₁ - 1
    let n : ℕ := Nat.floor z₂
    have hDlog : D ≤ log z₁ := by
      have := Real.log_le_log (Real.exp_pos D) hlarge
      simpa using this
    have hz₁four : 4 ≤ z₁ := by
      calc
        (4 : ℝ) ≤ D + 1 := by linarith
        _ ≤ exp D := Real.add_one_le_exp D
        _ ≤ z₁ := hlarge
    have hfloor_four : 4 ≤ Nat.floor z₁ := Nat.le_floor hz₁four
    have hkhalf : z₁ / 2 ≤ (k : ℝ) := by
      have hfloor := Nat.lt_floor_add_one z₁
      have hkcast : (k : ℝ) = (Nat.floor z₁ : ℝ) - 1 := by
        dsimp [k]
        rw [Nat.cast_sub (by omega : 1 ≤ Nat.floor z₁)]
        norm_num
      rw [hkcast]
      nlinarith
    have hkz₁ : (k : ℝ) < z₁ := by
      have hfloor : (Nat.floor z₁ : ℝ) ≤ z₁ :=
        Nat.floor_le (by linarith)
      have hklt : k < Nat.floor z₁ := by
        dsimp [k]
        omega
      exact lt_of_lt_of_le (by exact_mod_cast hklt) hfloor
    have hkp : k < p := by
      have : (k : ℝ) < (p : ℝ) := lt_of_lt_of_le hkz₁ hpz₁
      exact_mod_cast this
    have hpn : p ≤ n := by
      have : p < n + 1 := by
        have hcast : (p : ℝ) < (n : ℝ) + 1 := by
          dsimp [n]
          exact lt_trans hpz₂ (Nat.lt_floor_add_one z₂)
        exact_mod_cast hcast
      omega
    have hk2 : 2 ≤ k := by
      have : (2 : ℝ) ≤ (k : ℝ) := by nlinarith [hkhalf, hz₁four]
      exact_mod_cast this
    have hkn : k ≤ n := le_trans (le_of_lt hkp) hpn
    have hbound := hinterval k n hk2 hkn s (by
      intro q hq
      refine ⟨(hs q hq).1, ?_, ?_⟩
      · have : (k : ℝ) < (q : ℝ) :=
          lt_of_lt_of_le hkz₁ (hsinterval q hq).1
        exact_mod_cast this
      · have hqfloor := Nat.lt_floor_add_one z₂
        have : q < n + 1 := by
          have hcast : (q : ℝ) < (n : ℝ) + 1 := by
            dsimp [n]
            exact lt_trans (hsinterval q hq).2 hqfloor
          exact_mod_cast hcast
        omega)
    have hlogk : 0 < log (k : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < k by omega)
    have hlogk_le : log (k : ℝ) ≤ log z₁ :=
      Real.log_le_log (by positivity) (le_of_lt hkz₁)
    have hlogk_lower : log z₁ - log 2 ≤ log (k : ℝ) := by
      calc
        log z₁ - log 2 = log (z₁ / 2) := by
          rw [Real.log_div (ne_of_gt (by linarith : 0 < z₁)) (by norm_num)]
        _ ≤ log (k : ℝ) := Real.log_le_log (by positivity) hkhalf
    have hlogk_half : log z₁ / 2 ≤ log (k : ℝ) := by
      dsimp [D, A] at hDlog
      nlinarith
    have hAdiv : A / log (k : ℝ) ≤ 2 * A / log z₁ := by
      apply (div_le_div_iff₀ hlogk hlogz₁).mpr
      have := mul_le_mul_of_nonneg_left hlogk_half hA
      nlinarith
    have hlogratio : log (log z₁ / log (k : ℝ)) ≤ 2 * log 2 / log z₁ := by
      have hratio : 0 < log z₁ / log (k : ℝ) := div_pos hlogz₁ hlogk
      calc
        log (log z₁ / log (k : ℝ)) ≤ log z₁ / log (k : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hratio
        _ = (log z₁ - log (k : ℝ)) / log (k : ℝ) := by
          field_simp
        _ ≤ log 2 / log (k : ℝ) := by
          apply div_le_div_of_nonneg_right
            (by linarith [hlogk_le, hlogk_lower]) (le_of_lt hlogk)
        _ ≤ 2 * log 2 / log z₁ := by
          apply (div_le_div_iff₀ hlogk hlogz₁).mpr
          have := mul_le_mul_of_nonneg_left hlogk_half (le_of_lt hlog2)
          nlinarith
    have hnlez₂ : (n : ℝ) ≤ z₂ := by
      dsimp [n]
      exact Nat.floor_le (by linarith)
    have hlogn : 0 < log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hlogn_le : log (n : ℝ) ≤ log z₂ :=
      Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hnlez₂
    have hinner :
        log (log (n : ℝ) / log (k : ℝ)) ≤ log (log z₂ / log (k : ℝ)) :=
      Real.log_le_log (div_pos hlogn hlogk)
        (div_le_div_of_nonneg_right hlogn_le (le_of_lt hlogk))
    have hsplit :
        log (log z₂ / log (k : ℝ)) =
          log (log z₂ / log z₁) + log (log z₁ / log (k : ℝ)) := by
      rw [Real.log_div hlogz₂.ne' hlogk.ne',
        Real.log_div hlogz₂.ne' hlogz₁.ne',
        Real.log_div hlogz₁.ne' hlogk.ne']
      ring
    have hlogprod :
        log (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          log (log z₂ / log z₁) + D / log z₁ := by
      calc
        log (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
            log (log (n : ℝ) / log (k : ℝ)) + A / log (k : ℝ) := by
              simpa only [A] using hbound
        _ ≤ log (log z₂ / log (k : ℝ)) + A / log (k : ℝ) :=
          add_le_add hinner le_rfl
        _ = log (log z₂ / log z₁) +
              (log (log z₁ / log (k : ℝ)) + A / log (k : ℝ)) := by
          rw [hsplit]
          ring
        _ ≤ log (log z₂ / log z₁) +
              (2 * log 2 / log z₁ + 2 * A / log z₁) :=
          by linarith [add_le_add hlogratio hAdiv]
        _ = log (log z₂ / log z₁) + D / log z₁ := by
          dsimp [D]
          ring
    have hxnonneg : 0 ≤ D / log z₁ := div_nonneg (le_of_lt hD) (le_of_lt hlogz₁)
    have hxle : D / log z₁ ≤ 1 := (div_le_one₀ hlogz₁).mpr hDlog
    have hexp : exp (D / log z₁) ≤ 1 + 2 * D / log z₁ := by
      have habs : |D / log z₁| ≤ 1 := by
        rw [abs_of_nonneg hxnonneg]
        exact hxle
      have h := Real.abs_exp_sub_one_le habs
      rw [abs_of_nonneg hxnonneg] at h
      have h' : |exp (D / log z₁) - 1| ≤ 2 * D / log z₁ := by
        calc
          |exp (D / log z₁) - 1| ≤ 2 * (D / log z₁) := h
          _ = 2 * D / log z₁ := by ring
      have hself : exp (D / log z₁) - 1 ≤ |exp (D / log z₁) - 1| :=
        le_abs_self _
      calc
        exp (D / log z₁) = (exp (D / log z₁) - 1) + 1 := by ring
        _ ≤ |exp (D / log z₁) - 1| + 1 := add_le_add_left hself _
        _ ≤ 2 * D / log z₁ + 1 := add_le_add_left h' _
        _ = 1 + 2 * D / log z₁ := by ring
    have hprodexp :
        (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          (log z₂ / log z₁) * exp (D / log z₁) := by
      have := Real.exp_le_exp.mpr hlogprod
      rw [Real.exp_log hprodpos, Real.exp_add,
        Real.exp_log hratio_pos] at this
      exact this
    have hKlarge : 2 * D ≤ K := by
      dsimp [K]
      nlinarith
    calc
      (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          (log z₂ / log z₁) * exp (D / log z₁) := hprodexp
      _ ≤ (log z₂ / log z₁) * (1 + 2 * D / log z₁) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hratio_pos)
      _ ≤ (log z₂ / log z₁) * (1 + K / log z₁) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hratio_pos)
        have hdiv : 2 * D / log z₁ ≤ K / log z₁ :=
          div_le_div_of_nonneg_right hKlarge (le_of_lt hlogz₁)
        linarith
  · let n : ℕ := Nat.floor z₂
    have hp2 : 2 < p := (hs p hp).2
    have hpn : p ≤ n := by
      have : p < n + 1 := by
        have hcast : (p : ℝ) < (n : ℝ) + 1 := by
          dsimp [n]
          exact lt_trans hpz₂ (Nat.lt_floor_add_one z₂)
        exact_mod_cast hcast
      omega
    have hn2 : 2 ≤ n := by omega
    have hbound := hinterval 2 n (by norm_num) hn2 s (by
      intro q hq
      refine ⟨(hs q hq).1, (hs q hq).2, ?_⟩
      have hqfloor := Nat.lt_floor_add_one z₂
      have : q < n + 1 := by
        have hcast : (q : ℝ) < (n : ℝ) + 1 := by
          dsimp [n]
          exact lt_trans (hsinterval q hq).2 hqfloor
        exact_mod_cast hcast
      omega)
    have hsmalllog : log z₁ ≤ D := by
      have hz₁exp : z₁ ≤ exp D := le_of_lt (lt_of_not_ge hlarge)
      have := Real.log_le_log (by linarith : 0 < z₁) hz₁exp
      simpa using this
    have hnlez₂ : (n : ℝ) ≤ z₂ := by
      dsimp [n]
      exact Nat.floor_le (by linarith)
    have hlogn : 0 < log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hlogn_le : log (n : ℝ) ≤ log z₂ :=
      Real.log_le_log (by positivity) hnlez₂
    have hlogndiv : log (n : ℝ) / log 2 ≤ log z₂ / log 2 :=
      div_le_div_of_nonneg_right hlogn_le (le_of_lt hlog2)
    have hsplit :
        log z₂ / log 2 =
          (log z₂ / log z₁) * (log z₁ / log 2) := by
      field_simp
    have hz₁div : log z₁ / log 2 ≤ D / log 2 :=
      div_le_div_of_nonneg_right hsmalllog (le_of_lt hlog2)
    have hlogprod :
        log (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          log (log (n : ℝ) / log 2) + A / log 2 := by
      simpa [A] using hbound
    have hprodexp :
        (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          (log (n : ℝ) / log 2) * exp (A / log 2) := by
      have h := Real.exp_le_exp.mpr hlogprod
      rw [Real.exp_log hprodpos, Real.exp_add,
        Real.exp_log (div_pos hlogn hlog2)] at h
      exact h
    have hprodE :
        (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          (log z₂ / log z₁) * E := by
      calc
        (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
            (log (n : ℝ) / log 2) * exp (A / log 2) := hprodexp
        _ ≤ (log z₂ / log 2) * exp (A / log 2) :=
          mul_le_mul_of_nonneg_right hlogndiv (by positivity)
        _ = (log z₂ / log z₁) *
              ((log z₁ / log 2) * exp (A / log 2)) := by
          rw [hsplit]
          ring
        _ ≤ (log z₂ / log z₁) *
              ((D / log 2) * exp (A / log 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hz₁div (by positivity))
            (le_of_lt hratio_pos)
        _ = (log z₂ / log z₁) * E := by rfl
    have hKE : E ≤ K / log z₁ := by
      apply (le_div_iff₀ hlogz₁).mpr
      calc
        E * log z₁ ≤ E * D :=
          mul_le_mul_of_nonneg_left hsmalllog (le_of_lt hE)
        _ ≤ K := by
          dsimp [K]
          nlinarith
    calc
      (∏ q ∈ s, (1 - 1 / ((q : ℝ) - 1))⁻¹) ≤
          (log z₂ / log z₁) * E := hprodE
      _ ≤ (log z₂ / log z₁) * (1 + K / log z₁) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hratio_pos)


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
