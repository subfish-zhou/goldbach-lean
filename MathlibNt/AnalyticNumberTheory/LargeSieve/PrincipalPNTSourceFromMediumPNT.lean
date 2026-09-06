import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimeAPSourceClosure
import PrimeNumberTheoremAnd.MediumPNT

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter Set
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- At modulus one the principal character prefix is literally the real
Chebyshev `ψ` value at the integer endpoint. -/
theorem coprimeLambdaPrefix_one_eq_psi (y : ℕ) :
    coprimeLambdaPrefix y 1 = (Chebyshev.psi (y : ℝ) : ℂ) := by
  rw [coprimeLambdaPrefix, Chebyshev.psi_eq_sum_range]
  push_cast
  simp [lambdaNatCoeff]

/-- Exact pointwise bridge from the production principal error at modulus one
to the authoritative real-valued PNT error. -/
theorem norm_principalLambdaMainError_one_eq_psi_sub (y : ℕ) :
    ‖principalLambdaMainError y 1‖ =
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| := by
  rw [principalLambdaMainError, coprimeLambdaPrefix_one_eq_psi]
  rw [← Complex.ofReal_natCast]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Exact finite bridge, including the production prefix maximum. -/
theorem principalLambdaPrefixMaxError_one_eq_psi_prefixMax (N : ℕ) :
    principalLambdaPrefixMaxError N 1 =
      ((Finset.range (N + 1)).image
        (fun (y : ℕ) => |Chebyshev.psi (y : ℝ) - (y : ℝ)|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold principalLambdaPrefixMaxError
  simp_rw [norm_principalLambdaMainError_one_eq_psi_sub]

/-! ## Deterministic discrete-Abel versus true-li source -/

/-- The Abel main term telescopes exactly to the reciprocal-log Riemann sum. -/
theorem discreteAbelLiMain_eq_sum_reciprocalLogWeight (y : ℕ) :
    discreteAbelLiMain y =
      ∑ n ∈ Finset.range (y + 1), reciprocalLogWeight n := by
  induction y with
  | zero => simp [discreteAbelLiMain, reciprocalLogWeight]
  | succ y ih =>
      rw [discreteAbelLiMain, Finset.sum_range_succ]
      rw [show (y + 1 + 1 : ℕ) = (y + 1) + 1 by omega,
        Finset.sum_range_succ, ← ih]
      unfold discreteAbelLiMain
      norm_num
      ring

private lemma reciprocalLog_integral_unit_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / Real.log (n + 1 : ℝ) ≤
        ∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t ∧
      (∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t) ≤
        1 / Real.log (n : ℝ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≤ n + 1 := by norm_num
  have hint :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable_of_two_le
      hnreal hnn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  constructor
  · calc
      1 / Real.log (n + 1 : ℝ) =
          ∫ _t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log (n + 1 : ℝ) := by
            simp [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t := by
        apply intervalIntegral.integral_mono_on hnn intervalIntegrable_const hint
        intro t ht
        apply one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
        exact Real.log_le_log (by linarith [ht.1]) ht.2
  · calc
      (∫ t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log t) ≤
          ∫ _t in (n : ℝ)..(n + 1 : ℝ), 1 / Real.log (n : ℝ) := by
        apply intervalIntegral.integral_mono_on hnn hint intervalIntegrable_const
        intro t ht
        apply one_div_le_one_div_of_le hlogn
        exact Real.log_le_log (by linarith) ht.1
      _ = 1 / Real.log (n : ℝ) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]

/-- The discrete reciprocal-log sum differs from the integral by a bounded
endpoint correction.  This is a genuine integral comparison, not a source
assumption. -/
theorem discreteAbelLiMain_sub_integral_bounds {y : ℕ} (hy : 2 ≤ y) :
    1 / Real.log (y : ℝ) ≤ discreteAbelLiMain y -
        ∫ t in (2 : ℝ)..(y : ℝ), 1 / Real.log t ∧
      discreteAbelLiMain y -
          ∫ t in (2 : ℝ)..(y : ℝ), 1 / Real.log t ≤
        1 / Real.log 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hy
  induction k with
  | zero =>
      rw [discreteAbelLiMain_eq_sum_reciprocalLogWeight]
      norm_num [reciprocalLogWeight, Finset.sum_range_succ]
  | succ k ih =>
      let n : ℕ := 2 + k
      have hn : 2 ≤ n := by omega
      have hb := reciprocalLog_integral_unit_bounds n hn
      have hint₁ :=
        MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable
          (show (2 : ℝ) ≤ n by exact_mod_cast hn)
      have hint₂ :=
        MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable_of_two_le
          (show (2 : ℝ) ≤ n by exact_mod_cast hn) (show (n : ℝ) ≤ n + 1 by norm_num)
      have ih' := ih (by omega)
      rw [discreteAbelLiMain_eq_sum_reciprocalLogWeight,
        show 2 + (k + 1) = n + 1 by omega, Finset.sum_range_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
      change 1 / Real.log (n : ℝ) ≤ discreteAbelLiMain n -
          ∫ t in (2 : ℝ)..(n : ℝ), 1 / Real.log t ∧
        discreteAbelLiMain n -
            ∫ t in (2 : ℝ)..(n : ℝ), 1 / Real.log t ≤
          1 / Real.log 2 at ih'
      rw [← discreteAbelLiMain_eq_sum_reciprocalLogWeight n]
      have hw : reciprocalLogWeight (n + 1) = 1 / Real.log (n + 1 : ℝ) := by
        simp [reciprocalLogWeight, show 2 ≤ n + 1 by omega]
      rw [hw]
      constructor
      · linarith only [ih'.1, hb.2]
      · linarith only [ih'.2, hb.1]

/-- The genuine-li discrepancy is bounded by an absolute endpoint constant. -/
theorem globalChebyshevToLiSourceError_le_two_div_log_two
    {y : ℕ} (hy : 2 ≤ y) :
    globalChebyshevToLiSourceError y ≤ 2 / Real.log 2 := by
  have hb := discreteAbelLiMain_sub_integral_bounds hy
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [globalChebyshevToLiSourceError,
    MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral,
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral]
  rw [abs_le]
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have htwo : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog
  have hrel : 2 / Real.log 2 = 2 * (1 / Real.log 2) := by ring
  constructor
  · linarith only [hb.1, one_div_pos.mpr hlogy]
  · linarith only [hb.2, hrel, htwo]

/-- A uniform deterministic bound valid also at the two artificial low
endpoints of the prefix maximum. -/
noncomputable def globalLiDiscreteErrorBound : ℝ :=
  max (globalChebyshevToLiSourceError 0)
    (max (globalChebyshevToLiSourceError 1) (2 / Real.log 2))

theorem globalChebyshevToLiSourceError_le_bound (y : ℕ) :
    globalChebyshevToLiSourceError y ≤ globalLiDiscreteErrorBound := by
  by_cases hy : 2 ≤ y
  · exact (globalChebyshevToLiSourceError_le_two_div_log_two hy).trans
      (le_max_of_le_right (le_max_right _ _))
  · interval_cases y
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_left _ _)

theorem globalChebyshevToLiSourcePrefixMaxError_le_bound (N : ℕ) :
    globalChebyshevToLiSourcePrefixMaxError N ≤ globalLiDiscreteErrorBound := by
  unfold globalChebyshevToLiSourcePrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, _hy, rfl⟩
  exact globalChebyshevToLiSourceError_le_bound y

private lemma reciprocalLogWeight_nonneg (n : ℕ) : 0 ≤ reciprocalLogWeight n := by
  unfold reciprocalLogWeight
  split_ifs with hn
  · exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · rfl

private lemma reciprocalLogWeight_succ_le {n : ℕ} (hn : 2 ≤ n) :
    reciprocalLogWeight (n + 1) ≤ reciprocalLogWeight n := by
  simp only [reciprocalLogWeight, if_pos hn, if_pos (show 2 ≤ n + 1 by omega)]
  apply inv_anti₀
  · exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  · exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by norm_num)

/-- The total variation of the reciprocal-log Abel kernel is an absolute
constant: after its jump at `2`, the weight is nonnegative and decreasing. -/
theorem discreteAbelAmplifier_le_two_div_log_two (y : ℕ) :
    discreteAbelAmplifier y ≤ 2 / Real.log 2 := by
  by_cases hy : y < 2
  · interval_cases y <;> norm_num [discreteAbelAmplifier, reciprocalLogWeight] <;> positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ y by omega)
    induction k with
    | zero =>
        norm_num [discreteAbelAmplifier, reciprocalLogWeight, Finset.sum_range_succ]
        have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        rw [abs_of_pos hlog]
        rw [div_eq_mul_inv]
        linarith
    | succ k ih =>
        let n : ℕ := 2 + k
        have hn : 2 ≤ n := by omega
        have hmono := reciprocalLogWeight_succ_le hn
        have hnon := reciprocalLogWeight_nonneg n
        have hnons := reciprocalLogWeight_nonneg (n + 1)
        rw [show 2 + (k + 1) = n + 1 by omega]
        unfold discreteAbelAmplifier
        rw [Finset.sum_range_succ, abs_of_nonneg hnons,
          abs_of_nonneg (sub_nonneg.mpr hmono)]
        have ih' := ih (by omega)
        change discreteAbelAmplifier n ≤ 2 / Real.log 2 at ih'
        unfold discreteAbelAmplifier at ih'
        rw [abs_of_nonneg hnon] at ih'
        linarith [ih']

theorem discreteAbelAmplifierPrefixMax_le_two_div_log_two (N : ℕ) :
    discreteAbelAmplifierPrefixMax N ≤ 2 / Real.log 2 := by
  unfold discreteAbelAmplifierPrefixMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, _hy, rfl⟩
  exact discreteAbelAmplifier_le_two_div_log_two y

/-! ## Uniform logarithmic payment -/

/-- Any real power of `log x` is eventually bounded by `sqrt x`. -/
private lemma eventually_log_rpow_le_sqrt (A : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ A ≤ Real.sqrt x := by
  have h :=
    (isLittleO_log_rpow_rpow_atTop A (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1.le) A),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) (1 / 2 : ℝ)),
    one_mul, ← Real.sqrt_eq_rpow] at hx
  exact hx

/-- The square-root range is negligible compared with `x / log(x)^A`. -/
private lemma eventually_sqrt_le_div_log_rpow (A : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.sqrt x ≤ x / Real.log x ^ A := by
  filter_upwards [eventually_log_rpow_le_sqrt A,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hlog hx
  have hx0 : 0 ≤ x := by linarith
  have hl0 : 0 < Real.log x ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos hx) A
  rw [le_div_iff₀ hl0]
  calc
    Real.sqrt x * Real.log x ^ A ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx0

/-- Stretched-exponential decay pays an arbitrary real logarithmic power. -/
private lemma eventually_log_rpow_mul_exp_le_one
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ A * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) ≤ 1 := by
  have hp : (0 : ℝ) < 1 / 10 := by norm_num
  have hsmall :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop hp).bound (div_pos hc hA))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Real.exp 1)] with x hx hxlarge
  have hexp1 : 1 < x := by
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hlog : 0 < Real.log x := Real.log_pos hexp1
  have hlogone : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hxlarge
  have hpow0 : 0 ≤ Real.log x ^ (1 / 10 : ℝ) :=
    Real.rpow_nonneg hlog.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hlogone.le),
    Real.norm_eq_abs, abs_of_nonneg hpow0] at hx
  have hscaled : A * Real.log (Real.log x) ≤
      c * Real.log x ^ (1 / 10 : ℝ) := by
    calc
      A * Real.log (Real.log x) ≤
          A * ((c / A) * Real.log x ^ (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx hA.le
      _ = c * Real.log x ^ (1 / 10 : ℝ) := by field_simp
  rw [Real.rpow_def_of_pos hlog, ← Real.exp_add]
  calc
    Real.exp (Real.log (Real.log x) * A +
        -c * Real.log x ^ (1 / 10 : ℝ)) ≤ Real.exp 0 := by
      rw [Real.exp_le_exp]
      nlinarith
    _ = 1 := Real.exp_zero

/-- The same payment after replacing `log y` by half of `log N`; this is the
large-prefix branch used below. -/
private lemma eventually_half_log_exp_le_inv_log_rpow
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-(c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ)) *
          Real.log x ^ (1 / 10 : ℝ)) ≤ (Real.log x ^ A)⁻¹ := by
  have hd : 0 < c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ) := by positivity
  filter_upwards [eventually_log_rpow_mul_exp_le_one A
    (c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ)) hA hd,
    Filter.eventually_gt_atTop 1] with x hx hx1
  have hlogpow : 0 < Real.log x ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos hx1) A
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hlogpow).2
  simpa [mul_comm] using hx

/-- `MediumPNT`, made uniform over the genuine production prefix maximum. -/
theorem principalLambdaPrefixMaxError_one_eventually_le (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        principalLambdaPrefixMaxError N 1 ≤
          K * (N : ℝ) / Real.log N ^ A := by
  obtain ⟨c, hc, hmedium⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff'] at hmedium
  obtain ⟨M, hM, hmedium⟩ := hmedium
  let d : ℝ := c * (1 / 2 : ℝ) ^ (1 / 10 : ℝ)
  let Ksmall : ℝ := Real.log 4 + 5
  have hKsmall : 0 < Ksmall := by dsimp [Ksmall]; positivity
  let K : ℝ := M + Ksmall
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hmediumNat : ∀ᶠ y : ℕ in Filter.atTop,
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
        M * ((y : ℝ) * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := by
    have h := tendsto_natCast_atTop_atTop.eventually hmedium
    filter_upwards [h] with y hy
    have hnonneg : 0 ≤ (y : ℝ) *
        Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) := by positivity
    simpa [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hy
  rw [Filter.eventually_atTop] at hmediumNat
  obtain ⟨Y, hY⟩ := hmediumNat
  have hsqrtNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_sqrt_le_div_log_rpow A)
  have hexpNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_half_log_exp_le_inv_log_rpow A c hA hc)
  filter_upwards [hsqrtNat, hexpNat,
    Filter.eventually_ge_atTop (max (Y * Y) 2)] with N hsqrtPay hexpPay hNlarge
  rw [principalLambdaPrefixMaxError_one_eq_psi_prefixMax]
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hyRange, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hyRange)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hNlarge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN2)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbudget0 : 0 ≤ (N : ℝ) / Real.log N ^ A := by positivity
  by_cases hsmall : (y : ℝ) ≤ Real.sqrt N
  · have hpsi := Chebyshev.psi_le_const_mul_self (x := (y : ℝ)) (by positivity)
    have herr : |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤ Ksmall * (y : ℝ) := by
      rw [abs_sub_comm]
      calc
        |(y : ℝ) - Chebyshev.psi (y : ℝ)| ≤
            |(y : ℝ)| + |Chebyshev.psi (y : ℝ)| := abs_sub _ _
        _ = (y : ℝ) + Chebyshev.psi (y : ℝ) := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (Chebyshev.psi_nonneg _)]
        _ ≤ Ksmall * (y : ℝ) := by dsimp [Ksmall]; linarith
    calc
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤ Ksmall * (y : ℝ) := herr
      _ ≤ Ksmall * Real.sqrt N := mul_le_mul_of_nonneg_left hsmall hKsmall.le
      _ ≤ Ksmall * ((N : ℝ) / Real.log N ^ A) :=
        mul_le_mul_of_nonneg_left hsqrtPay hKsmall.le
      _ ≤ K * (N : ℝ) / Real.log N ^ A := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [hM])
          (by positivity)
  · have hsqrty : Real.sqrt N < y := lt_of_not_ge hsmall
    have hyY : Y ≤ y := by
      by_contra hyY
      have hylt : y < Y := Nat.lt_of_not_ge hyY
      have hySq : y * y < Y * Y := Nat.mul_self_lt_mul_self hylt
      have hYSqN : Y * Y ≤ N := le_trans (le_max_left _ _) hNlarge
      have hySqN : y * y < N := lt_of_lt_of_le hySq hYSqN
      have : (y : ℝ) < Real.sqrt N :=
        (Real.lt_sqrt (show 0 ≤ (y : ℝ) by positivity)).mpr (by
          norm_num [pow_two]
          exact_mod_cast hySqN)
      linarith
    have hpnt := hY y hyY
    have hlogLower : (1 / 2 : ℝ) * Real.log N ≤ Real.log y := by
      have hlogsqrt := Real.log_le_log (Real.sqrt_pos.2 hNpos) hsqrty.le
      rw [Real.log_sqrt hNpos.le] at hlogsqrt
      linarith
    have hhalf0 : 0 ≤ (1 / 2 : ℝ) * Real.log N := by positivity
    have hpowLower :
        (1 / 2 : ℝ) ^ (1 / 10 : ℝ) * Real.log N ^ (1 / 10 : ℝ) ≤
          Real.log y ^ (1 / 10 : ℝ) := by
      calc
        (1 / 2 : ℝ) ^ (1 / 10 : ℝ) * Real.log N ^ (1 / 10 : ℝ) =
            ((1 / 2 : ℝ) * Real.log N) ^ (1 / 10 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        _ ≤ Real.log y ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow hhalf0 hlogLower (by norm_num)
    have hexpCompare :
        Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) ≤
          Real.exp (-d * Real.log N ^ (1 / 10 : ℝ)) := by
      rw [Real.exp_le_exp]
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_left hpowLower hc.le]
    calc
      |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
          M * ((y : ℝ) * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := hpnt
      _ ≤ M * ((N : ℝ) * Real.exp (-d * Real.log N ^ (1 / 10 : ℝ))) := by
        gcongr
      _ ≤ M * ((N : ℝ) * (Real.log N ^ A)⁻¹) := by gcongr
      _ = M * (N : ℝ) / Real.log N ^ A := by rw [div_eq_mul_inv]; ring
      _ ≤ K * (N : ℝ) / Real.log N ^ A := by
        have hMK : M ≤ K := by dsimp [K]; linarith [hKsmall]
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hMK hbudget0

/-- Closed production source: the real `MediumPNT` theorem supplies the
principal modulus-one prefix, while the Abel kernel and true-`li` discrepancy
are discharged by the deterministic bounds above. -/
theorem globalChebyshevToLiPrincipalPNTSource :
    GlobalChebyshevToLiPrincipalPNTSourceContract := by
  intro A hA
  obtain ⟨K, hK, hprefix⟩ :=
    principalLambdaPrefixMaxError_one_eventually_le A hA
  let D : ℝ := 2 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  let B : ℝ := globalLiDiscreteErrorBound
  have hB : 0 ≤ B := by
    dsimp [B, globalLiDiscreteErrorBound]
    exact (abs_nonneg _).trans (le_max_left _ _)
  let C : ℝ := D * K + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hsqrtNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_sqrt_le_div_log_rpow A)
  filter_upwards [hprefix, hsqrtNat, Filter.eventually_ge_atTop 2] with N hprefix hsqrtPay hN
  intro _hNarg
  have hbudgetNonneg : 0 ≤ (N : ℝ) / Real.log N ^ A := by positivity
  have hbudgetOne : 1 ≤ (N : ℝ) / Real.log N ^ A := by
    calc
      (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by
        exact_mod_cast (show 1 ≤ N by omega))
      _ ≤ (N : ℝ) / Real.log N ^ A := hsqrtPay
  have hprincipalNonneg : 0 ≤ principalLambdaPrefixMaxError N 1 := by
    unfold principalLambdaPrefixMaxError
    have hm := Finset.max'_mem
      ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y 1‖))
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)
    rcases Finset.mem_image.mp hm with ⟨y, _hy, heq⟩
    rw [← heq]
    exact norm_nonneg _
  unfold globalPartialSummationSource
  calc
    discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 +
        globalChebyshevToLiSourcePrefixMaxError N ≤
      D * (K * (N : ℝ) / Real.log N ^ A) + B := by
        apply add_le_add
        · calc
            discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 ≤
                D * principalLambdaPrefixMaxError N 1 :=
              mul_le_mul_of_nonneg_right
                (discreteAbelAmplifierPrefixMax_le_two_div_log_two N)
                hprincipalNonneg
            _ ≤ D * (K * (N : ℝ) / Real.log N ^ A) :=
              mul_le_mul_of_nonneg_left hprefix hD.le
        · exact globalChebyshevToLiSourcePrefixMaxError_le_bound N
    _ ≤ (D * K + B) * ((N : ℝ) / Real.log N ^ A) := by
      rw [add_mul, mul_assoc, mul_div_assoc]
      have hBpay : B ≤ B * ((N : ℝ) / Real.log N ^ A) := by
        nth_rewrite 1 [← mul_one B]
        exact mul_le_mul_of_nonneg_left hbudgetOne hB
      linarith
    _ ≤ C * (N : ℝ) / Real.log N ^ A := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

end

end AnalyticNumberTheory.LargeSieve
