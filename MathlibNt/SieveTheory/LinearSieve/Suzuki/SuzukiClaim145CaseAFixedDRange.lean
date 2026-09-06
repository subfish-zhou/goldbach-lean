import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SmallDHighCoordinate
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ComparisonInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ScalarEventual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerFinal
import Mathlib.Analysis.SpecialFunctions.Exponential

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set Filter Topology

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

lemma caseA_lowerProfile_eventually_one
    {q : ℕ} {d C : ℝ} (hq : 2 ≤ q) (hd : 2 < d) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ (1 + x ^ d / Real.log (q : ℝ)) ^ x * x *
        proposition131iiLowerProfile C x := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hd2 : 0 < d - 2 := by linarith
  let A : ℝ := (C + Real.log (Real.log (q : ℝ))) / (d - 2)
  filter_upwards [eventually_ge_atTop (12 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop A] with x hx hlogA
  have hx0 : 0 < x := by linarith
  have hxhalf : 0 < x / 2 := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlogxhalf := Real.log_le_sub_one_of_pos hxhalf
  have hlogx : Real.log x ≤ x / 2 := by
    rw [show x = (x / 2) * 2 by ring, Real.log_mul (ne_of_gt hxhalf) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hlog3x : Real.log (3 * x) ≤ x := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx0)]
    linarith
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog3xpos : 0 < Real.log (3 * x) := Real.log_pos (by nlinarith)
  have hloglog : Real.log (Real.log (3 * x)) ≤ Real.log x :=
    Real.log_le_log hlog3xpos hlog3x
  have hconst : C + Real.log (Real.log (q : ℝ)) ≤
      (d - 2) * Real.log x := by
    have hm := mul_le_mul_of_nonneg_left hlogA hd2.le
    dsimp [A] at hm
    field_simp [ne_of_gt hd2] at hm
    linarith
  have hexponent : 0 ≤
      x * (d * Real.log x - Real.log (Real.log (q : ℝ))) + Real.log x +
        (-x * Real.log x - x * Real.log (Real.log (3 * x)) - C * x) := by
    have hx1 : 1 ≤ x := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hloglog hconst) hx0.le]
  have hbase : x ^ d / Real.log (q : ℝ) ≤
      1 + x ^ d / Real.log (q : ℝ) := by linarith
  have hquotpos : 0 < x ^ d / Real.log (q : ℝ) := by positivity
  have hbasepos : 0 < 1 + x ^ d / Real.log (q : ℝ) := by linarith
  have hpow : (x ^ d / Real.log (q : ℝ)) ^ x ≤
      (1 + x ^ d / Real.log (q : ℝ)) ^ x :=
    Real.rpow_le_rpow hquotpos.le hbase hx0.le
  have hform :
      (x ^ d / Real.log (q : ℝ)) ^ x * x *
          proposition131iiLowerProfile C x =
        Real.exp
          (x * (d * Real.log x - Real.log (Real.log (q : ℝ))) + Real.log x +
            (-x * Real.log x - x * Real.log (Real.log (3 * x)) - C * x)) := by
    unfold proposition131iiLowerProfile
    rw [Real.rpow_def_of_pos hquotpos, Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hx0 d))
      (ne_of_gt hlogq), Real.log_rpow hx0 d]
    calc
      Real.exp ((d * Real.log x - Real.log (Real.log (q : ℝ))) * x) * x *
          Real.exp (-x * Real.log x - x * Real.log (Real.log (3 * x)) - C * x) =
        Real.exp ((d * Real.log x - Real.log (Real.log (q : ℝ))) * x) *
          Real.exp (Real.log x) *
            Real.exp (-x * Real.log x - x * Real.log (Real.log (3 * x)) - C * x) := by
              rw [Real.exp_log hx0]
      _ = _ := by
        repeat' rw [← Real.exp_add]
        congr 1 <;> ring
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp _ := Real.exp_le_exp.mpr hexponent
    _ = (x ^ d / Real.log (q : ℝ)) ^ x * x *
        proposition131iiLowerProfile C x := hform.symm
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow hx0.le)
        (Real.exp_pos _).le

lemma section13Hat_uniform_pos_on_compact
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {M : ℝ} (hM : 2 ≤ M) :
    ∃ e : ℝ, 0 < e ∧ ∀ sign x, x ∈ Set.Icc (2 : ℝ) M → e ≤ H.T sign x := by
  have hcont (sign : ErrorSign) :
      ContinuousOn (H.T sign) (Set.Icc (2 : ℝ) M) :=
    (hH.continuous sign).mono (by intro x hx; exact hx.1.trans_lt' (by norm_num))
  have hne : (Set.Icc (2 : ℝ) M).Nonempty := Set.nonempty_Icc.mpr hM
  obtain ⟨xp, hxp, hp⟩ := isCompact_Icc.exists_isMinOn hne (hcont .plus)
  obtain ⟨xm, hxm, hm⟩ := isCompact_Icc.exists_isMinOn hne (hcont .minus)
  let e := min (H.T .plus xp) (H.T .minus xm)
  have hep : 0 < H.T .plus xp := hH.positive .plus xp (by linarith [hxp.1])
  have hem : 0 < H.T .minus xm := hH.positive .minus xm (by linarith [hxm.1])
  refine ⟨e, lt_min hep hem, ?_⟩
  intro sign x hx
  cases sign with
  | plus => exact (min_le_left _ _).trans (hp hx)
  | minus => exact (min_le_right _ _).trans (hm hx)

private lemma exists_caseA_errorEnvelope_lower_for_fixed_q
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 2 < d) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ (depth : ℕ) (coord : ℝ),
      2 ≤ coord → e0 ≤ errorEnvelope H depth (q : ℝ) d coord := by
  rcases proposition131iiUniformQuantitativeLower_of_source hH with
    ⟨C, M0, hC, hM0, hprop⟩
  have hgrowth := caseA_lowerProfile_eventually_one (q := q) (C := C) hq hd
  rcases eventually_atTop.1 hgrowth with ⟨R, hR⟩
  let M : ℝ := max M0 (max R 2)
  have hM2 : 2 ≤ M := (le_max_right R 2).trans (le_max_right M0 (max R 2))
  obtain ⟨e, he, heLower⟩ := section13Hat_uniform_pos_on_compact hH.toSection13HatContract hM2
  let e0 : ℝ := min 1 (2 * e)
  have he0 : 0 < e0 := lt_min (by norm_num) (by positivity)
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  refine ⟨e0, he0, ?_⟩
  intro depth coord hcoord
  have hcoord0 : 0 < coord := by linarith
  have hbase : 1 ≤ 1 + coord ^ d / Real.log (q : ℝ) := by
    have : 0 ≤ coord ^ d / Real.log (q : ℝ) := by positivity
    linarith
  have hbasepow : 1 ≤ (1 + coord ^ d / Real.log (q : ℝ)) ^ coord :=
    Real.one_le_rpow hbase hcoord0.le
  by_cases hcoordM : M ≤ coord
  · have hprof : proposition131iiLowerProfile C coord ≤ H.T (ErrorSign.ofDepth depth) coord :=
      hprop _ _ ((le_max_left M0 (max R 2)).trans hcoordM)
    have hone : 1 ≤ (1 + coord ^ d / Real.log (q : ℝ)) ^ coord * coord *
        proposition131iiLowerProfile C coord :=
      hR coord ((le_max_left R 2).trans ((le_max_right M0 (max R 2)).trans hcoordM))
    have hEnvelope : 1 ≤ (1 + coord ^ d / Real.log (q : ℝ)) ^ coord * coord *
        H.T (ErrorSign.ofDepth depth) coord :=
      hone.trans (mul_le_mul_of_nonneg_left hprof
        (mul_nonneg (zero_le_one.trans hbasepow) hcoord0.le))
    unfold errorEnvelope Section13HatLayers.kappaHat
    norm_num [Real.rpow_one]
    exact (min_le_left _ _).trans hEnvelope
  · have hcompact : coord ∈ Set.Icc (2 : ℝ) M := ⟨hcoord, le_of_not_ge hcoordM⟩
    have hT := heLower (ErrorSign.ofDepth depth) coord hcompact
    have hTx : 2 * e ≤ (1 + coord ^ d / Real.log (q : ℝ)) ^ coord * coord *
        H.T (ErrorSign.ofDepth depth) coord := by
      have hpow0 : 0 ≤ (1 + coord ^ d / Real.log (q : ℝ)) ^ coord :=
        zero_le_one.trans hbasepow
      have hmul := mul_le_mul hbasepow hT he.le hpow0
      calc
        2 * e ≤ coord * e := mul_le_mul_of_nonneg_right hcoord he.le
        _ ≤ coord * ((1 + coord ^ d / Real.log (q : ℝ)) ^ coord *
            H.T (ErrorSign.ofDepth depth) coord) :=
          mul_le_mul_of_nonneg_left (by simpa using hmul) hcoord0.le
        _ = _ := by ring
    unfold errorEnvelope Section13HatLayers.kappaHat
    norm_num [Real.rpow_one]
    exact (min_le_right _ _).trans hTx

lemma exists_caseA_scalar_constant_for_fixed_q
    (S : BoundingSieve) (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {q : ℕ} (hq : 2 ≤ q) {d Δ K : ℝ} (hd : 2 < d) (hK : 0 < K) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n p : ℕ) (x : ℝ),
      p = ⌈(q : ℝ) ^ (1 / x)⌉₊ → 2 ≤ x →
      suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
            ((⌊x - 2⌋₊ + 1).factorial : ℝ) *
          Real.exp (suzukiSourceL (p : ℝ) K) ≤
        A * claim14_5Scale S H n (q : ℝ) d Δ
          (sourceSigma (q : ℝ) d) K x := by
  obtain ⟨e0, he0, hEnvelopeLower⟩ :=
    exists_caseA_errorEnvelope_lower_for_fixed_q H hH hq hd
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hsigma : 0 < sourceSigma (q : ℝ) d := sourceSigma_pos_of_nat_two_le hq
  have hV : 0 < claim14_5VProduct S (q : ℝ) := by
    simpa [claim14_5VProduct, suzukiVProduct] using suzukiVProduct_pos S (q : ℝ)
  let B : ℝ := claim14_5VProduct S (q : ℝ) *
      (Real.exp (Real.sqrt K) / (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
      e0 * (Real.log (q : ℝ)) ^ (-Δ)
  have hB : 0 < B := by dsimp [B]; positivity
  let Lq : ℝ := suzukiSourceL (q : ℝ) K
  let A : ℝ := Real.exp (2 * Lq) / B
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro n p x hp hx
  have hx0 : 0 < x := by linarith
  have hpq : p ≤ q := by
    rw [hp]
    exact claim145_natCeil_rpow_le hq hx
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hpow : (1 : ℝ) < (q : ℝ) ^ (1 / x) :=
      Real.one_lt_rpow hq1 (one_div_pos.mpr hx0)
    have : 1 < ⌈(q : ℝ) ^ (1 / x)⌉₊ := (Nat.lt_ceil).mpr (by simpa using hpow)
    omega
  let Lp : ℝ := suzukiSourceL (p : ℝ) K
  have hLp : 0 < Lp := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogp : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < (p : ℝ) by exact_mod_cast (show 0 < p by omega))
        (by exact_mod_cast hp2)
    have hfirst : 0 ≤ Real.log (Real.log (p : ℝ) / Real.log 2) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hlog2).2 (by simpa using hlogp)
    have hsecond : 0 < Real.log (1 + K / Real.log 2) := by
      apply Real.log_pos
      have : 0 < K / Real.log 2 := div_pos hK hlog2
      linarith
    dsimp [Lp, suzukiSourceL]
    linarith
  have hLpq : Lp ≤ Lq := by
    dsimp [Lp, Lq]
    exact suzukiSourceL_mono (by exact_mod_cast (show 1 < p by omega)) (by exact_mod_cast hpq)
  have hleft :
      Lp ^ (⌊x - 2⌋₊ + 1) / (((⌊x - 2⌋₊ + 1).factorial : ℕ) : ℝ) *
          Real.exp Lp ≤ Real.exp (2 * Lq) := by
    have hterm := Real.pow_div_factorial_le_exp Lp hLp.le (⌊x - 2⌋₊ + 1)
    calc
      _ ≤ Real.exp Lp * Real.exp Lp :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_pos Lp).le
      _ = Real.exp (2 * Lp) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * Lq) := Real.exp_le_exp.mpr (by linarith)
  have hEnvelope : e0 ≤ errorEnvelope H n (q : ℝ) d x :=
    hEnvelopeLower n x hx
  have hscale : B ≤ claim14_5Scale S H n (q : ℝ) d Δ
      (sourceSigma (q : ℝ) d) K x := by
    unfold claim14_5Scale
    dsimp [B]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEnvelope (by positivity))
      (Real.rpow_nonneg hlogq.le _)
  calc
    _ ≤ Real.exp (2 * Lq) := by simpa [Lp] using hleft
    _ = A * B := by dsimp [A]; field_simp [ne_of_gt hB]
    _ ≤ A * claim14_5Scale S H n (q : ℝ) d Δ
        (sourceSigma (q : ℝ) d) K x := mul_le_mul_of_nonneg_left hscale hA.le

/-- Fixed-quotient scalar comparison with its coefficient chosen before the
varying sieve.  Uniformity is paid by the local-product hypothesis at `K`. -/
lemma exists_caseA_scalar_constant_for_fixed_q_uniform_in_S
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {q : ℕ} (hq : 2 ≤ q) {d Δ K : ℝ} (hd : 2 < d) (hK : 0 < K) :
    ∃ A : ℝ, 0 < A ∧ ∀ (S : BoundingSieve),
      HasDimensionOneLocalProductBound S K →
      ∀ (n p : ℕ) (x : ℝ),
      p = ⌈(q : ℝ) ^ (1 / x)⌉₊ → 2 ≤ x →
      suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
            ((⌊x - 2⌋₊ + 1).factorial : ℝ) *
          Real.exp (suzukiSourceL (p : ℝ) K) ≤
        A * claim14_5Scale S H n (q : ℝ) d Δ
          (sourceSigma (q : ℝ) d) K x := by
  obtain ⟨e0, he0, hEnvelopeLower⟩ :=
    exists_caseA_errorEnvelope_lower_for_fixed_q H hH hq hd
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hsigma : 0 < sourceSigma (q : ℝ) d := sourceSigma_pos_of_nat_two_le hq
  let Rq : ℝ := (Real.log (q : ℝ) / Real.log 2) * (1 + K / Real.log 2)
  have hRq : 0 < Rq := by dsimp [Rq]; positivity
  let B0 : ℝ := (1 / Rq) *
      (Real.exp (Real.sqrt K) / (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
      e0 * (Real.log (q : ℝ)) ^ (-Δ)
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  let Lq : ℝ := suzukiSourceL (q : ℝ) K
  let A : ℝ := Real.exp (2 * Lq) / B0
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro S hlocal n p x hp hx
  have hx0 : 0 < x := by linarith
  have hpq : p ≤ q := by rw [hp]; exact claim145_natCeil_rpow_le hq hx
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hpow : (1 : ℝ) < (q : ℝ) ^ (1 / x) :=
      Real.one_lt_rpow hq1 (one_div_pos.mpr hx0)
    have : 1 < ⌈(q : ℝ) ^ (1 / x)⌉₊ := (Nat.lt_ceil).mpr (by simpa using hpow)
    omega
  let Lp : ℝ := suzukiSourceL (p : ℝ) K
  have hLp : 0 < Lp := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogp : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < (p : ℝ) by exact_mod_cast (show 0 < p by omega))
        (by exact_mod_cast hp2)
    have hfirst : 0 ≤ Real.log (Real.log (p : ℝ) / Real.log 2) :=
      Real.log_nonneg ((le_div_iff₀ hlog2).2 (by simpa using hlogp))
    have hsecond : 0 < Real.log (1 + K / Real.log 2) := by
      apply Real.log_pos
      have : 0 < K / Real.log 2 := div_pos hK hlog2
      linarith
    dsimp [Lp, suzukiSourceL]
    linarith
  have hLpq : Lp ≤ Lq := by
    dsimp [Lp, Lq]
    exact suzukiSourceL_mono (by exact_mod_cast (show 1 < p by omega))
      (by exact_mod_cast hpq)
  have hleft :
      Lp ^ (⌊x - 2⌋₊ + 1) / (((⌊x - 2⌋₊ + 1).factorial : ℕ) : ℝ) *
          Real.exp Lp ≤ Real.exp (2 * Lq) := by
    have hterm := Real.pow_div_factorial_le_exp Lp hLp.le (⌊x - 2⌋₊ + 1)
    calc
      _ ≤ Real.exp Lp * Real.exp Lp :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_pos Lp).le
      _ = Real.exp (2 * Lp) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * Lq) := Real.exp_le_exp.mpr (by linarith)
  have hEnvelope : e0 ≤ errorEnvelope H n (q : ℝ) d x :=
    hEnvelopeLower n x hx
  have hVlower : 1 / Rq ≤ claim14_5VProduct S (q : ℝ) := by
    apply (div_le_iff₀ hRq).2
    simpa [Rq, mul_comm, mul_left_comm, mul_assoc] using
      (claim14_5VProduct_lower_of_localProduct
        (S := S) (D := (q : ℝ)) (K := K) (by exact_mod_cast hq) hlocal)
  have hscale : B0 ≤ claim14_5Scale S H n (q : ℝ) d Δ
      (sourceSigma (q : ℝ) d) K x := by
    unfold claim14_5Scale
    dsimp [B0]
    have hrest : 0 ≤ Real.exp (Real.sqrt K) /
        (Real.log (q : ℝ) * sourceSigma (q : ℝ) d) := by positivity
    have htail : 0 ≤ (Real.log (q : ℝ)) ^ (-Δ) := Real.rpow_nonneg hlogq.le _
    have hV0 : 0 ≤ claim14_5VProduct S (q : ℝ) :=
      (show 0 ≤ 1 / Rq by positivity).trans hVlower
    calc
      (1 / Rq) * (Real.exp (Real.sqrt K) /
          (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) * e0 *
          (Real.log (q : ℝ)) ^ (-Δ) ≤
        claim14_5VProduct S (q : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) * e0 *
          (Real.log (q : ℝ)) ^ (-Δ) := by gcongr
      _ ≤ claim14_5VProduct S (q : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
          errorEnvelope H n (q : ℝ) d x *
          (Real.log (q : ℝ)) ^ (-Δ) := by gcongr
  calc
    _ ≤ Real.exp (2 * Lq) := by simpa [Lp] using hleft
    _ = A * B0 := by dsimp [A]; field_simp [ne_of_gt hB0]
    _ ≤ A * claim14_5Scale S H n (q : ℝ) d Δ
        (sourceSigma (q : ℝ) d) K x := mul_le_mul_of_nonneg_left hscale hA.le

/-- A fixed finite quotient range admits one scalar constant, uniform in the
depth, quotient, natural-ceiling cutoff, and real coordinate. -/
theorem exists_claim145SmallDCaseAScalarComparison_of_fixedDmin
    (S : BoundingSieve) (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (Dmin : ℕ) {d Δ K C1 ΘK : ℝ} (hd : 2 < d) (hK : 0 < K)
    (hCaseA_lt : ∀ q : ℕ, 2 ≤ q →
      Real.log (q : ℝ) ≤ C1 * K ^ ΘK → q < Dmin) :
    ∃ C145 : ℝ, 0 < C145 ∧
      Claim145SmallDCaseAScalarComparison S H d Δ C145 K C1 ΘK := by
  classical
  let Aq : ℕ → ℝ := fun q => if hq : 2 ≤ q then
    Classical.choose (exists_caseA_scalar_constant_for_fixed_q S H hH hq (Δ := Δ) hd hK)
    else 0
  have hAq_pos : ∀ q : ℕ, 2 ≤ q → 0 < Aq q := by
    intro q hq
    dsimp only [Aq]
    rw [dif_pos hq]
    exact (Classical.choose_spec
      (exists_caseA_scalar_constant_for_fixed_q S H hH hq (Δ := Δ) hd hK)).1
  have hAq_bound : ∀ q : ℕ, 2 ≤ q → ∀ (n p : ℕ) (x : ℝ),
      p = ⌈(q : ℝ) ^ (1 / x)⌉₊ → 2 ≤ x →
      suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
            ((⌊x - 2⌋₊ + 1).factorial : ℝ) *
          Real.exp (suzukiSourceL (p : ℝ) K) ≤
        Aq q * claim14_5Scale S H n (q : ℝ) d Δ
          (sourceSigma (q : ℝ) d) K x := by
    intro q hq
    dsimp only [Aq]
    rw [dif_pos hq]
    exact (Classical.choose_spec
      (exists_caseA_scalar_constant_for_fixed_q S H hH hq (Δ := Δ) hd hK)).2
  let C145 : ℝ := 1 + ∑ q ∈ Finset.Ico 2 Dmin, Aq q
  have hsum0 : 0 ≤ ∑ q ∈ Finset.Ico 2 Dmin, Aq q := by
    apply Finset.sum_nonneg
    intro q hq
    exact (hAq_pos q (Finset.mem_Ico.mp hq).1).le
  have hC145 : 0 < C145 := by dsimp [C145]; linarith
  refine ⟨C145, hC145, ?_⟩
  intro n q p x hq hp hx hsmall
  have hqD : q < Dmin := hCaseA_lt q hq hsmall
  have hterm : Aq q ≤ ∑ a ∈ Finset.Ico 2 Dmin, Aq a := by
    apply Finset.single_le_sum
    · intro a ha
      exact (hAq_pos a (Finset.mem_Ico.mp ha).1).le
    · simp [hq, hqD]
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hscale0 : 0 ≤ claim14_5Scale S H n (q : ℝ) d Δ
      (sourceSigma (q : ℝ) d) K x := by
    have hx0 : 0 < x := by linarith
    have hsigma : 0 < sourceSigma (q : ℝ) d := sourceSigma_pos_of_nat_two_le hq
    have hE : 0 ≤ errorEnvelope H n (q : ℝ) d x :=
      errorEnvelope_nonneg H n hq1 hx0.le
        (hH.toSection13HatContract.positive _ x hx0).le
    unfold claim14_5Scale
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (suzukiVProduct_pos S (q : ℝ)).le
          (div_nonneg (Real.exp_pos _).le (mul_pos hlogq hsigma).le)) hE)
      (Real.rpow_nonneg hlogq.le _)
  exact (hAq_bound q hq n p x hp hx).trans
    (mul_le_mul_of_nonneg_right (by dsimp [C145]; linarith) hscale0)

/-- Uniform-in-sieve fixed-`Dmin` scalar producer.  Its finite maximum is formed
before `S`; the local-product contract is consumed only pointwise. -/
theorem exists_claim145SmallDCaseAScalarComparison_of_fixedDmin_uniform_in_S
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (Dmin : ℕ) {d Δ K C1 ΘK : ℝ} (hd : 2 < d) (hK : 0 < K)
    (hCaseA_lt : ∀ q : ℕ, 2 ≤ q →
      Real.log (q : ℝ) ≤ C1 * K ^ ΘK → q < Dmin) :
    ∃ C145 : ℝ, 0 < C145 ∧ ∀ S : BoundingSieve,
      HasDimensionOneLocalProductBound S K →
      Claim145SmallDCaseAScalarComparison S H d Δ C145 K C1 ΘK := by
  classical
  let Aq : ℕ → ℝ := fun q => if hq : 2 ≤ q then
    Classical.choose
      (exists_caseA_scalar_constant_for_fixed_q_uniform_in_S H hH hq (Δ := Δ) hd hK)
    else 0
  have hAq_pos : ∀ q : ℕ, 2 ≤ q → 0 < Aq q := by
    intro q hq
    dsimp only [Aq]
    rw [dif_pos hq]
    exact (Classical.choose_spec
      (exists_caseA_scalar_constant_for_fixed_q_uniform_in_S H hH hq
        (Δ := Δ) hd hK)).1
  have hAq_bound : ∀ q : ℕ, 2 ≤ q → ∀ S : BoundingSieve,
      HasDimensionOneLocalProductBound S K → ∀ (n p : ℕ) (x : ℝ),
      p = ⌈(q : ℝ) ^ (1 / x)⌉₊ → 2 ≤ x →
      suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
            ((⌊x - 2⌋₊ + 1).factorial : ℝ) *
          Real.exp (suzukiSourceL (p : ℝ) K) ≤
        Aq q * claim14_5Scale S H n (q : ℝ) d Δ
          (sourceSigma (q : ℝ) d) K x := by
    intro q hq
    dsimp only [Aq]
    rw [dif_pos hq]
    exact (Classical.choose_spec
      (exists_caseA_scalar_constant_for_fixed_q_uniform_in_S H hH hq
        (Δ := Δ) hd hK)).2
  let C145 : ℝ := 1 + ∑ q ∈ Finset.Ico 2 Dmin, Aq q
  have hsum0 : 0 ≤ ∑ q ∈ Finset.Ico 2 Dmin, Aq q := by
    apply Finset.sum_nonneg
    intro q hq
    exact (hAq_pos q (Finset.mem_Ico.mp hq).1).le
  have hC145 : 0 < C145 := by dsimp [C145]; linarith
  refine ⟨C145, hC145, ?_⟩
  intro S hlocal n q p x hq hp hx hsmall
  have hqD : q < Dmin := hCaseA_lt q hq hsmall
  have hterm : Aq q ≤ ∑ a ∈ Finset.Ico 2 Dmin, Aq a := by
    apply Finset.single_le_sum
    · intro a ha
      exact (hAq_pos a (Finset.mem_Ico.mp ha).1).le
    · simp [hq, hqD]
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hscale0 : 0 ≤ claim14_5Scale S H n (q : ℝ) d Δ
      (sourceSigma (q : ℝ) d) K x := by
    have hx0 : 0 < x := by linarith
    have hsigma : 0 < sourceSigma (q : ℝ) d := sourceSigma_pos_of_nat_two_le hq
    have hE : 0 ≤ errorEnvelope H n (q : ℝ) d x :=
      errorEnvelope_nonneg H n hq1 hx0.le
        (hH.toSection13HatContract.positive _ x hx0).le
    unfold claim14_5Scale
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (suzukiVProduct_pos S (q : ℝ)).le
          (div_nonneg (Real.exp_pos _).le (mul_pos hlogq hsigma).le)) hE)
      (Real.rpow_nonneg hlogq.le _)
  exact (hAq_bound q hq S hlocal n p x hp hx).trans
    (mul_le_mul_of_nonneg_right (by dsimp [C145]; linarith) hscale0)


end MathlibNt.SieveTheory
