import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ComparisonInternal

open scoped Classical BigOperators
open Filter Finset Topology
open Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3600000

/-- Suzuki p.83, Case B, uniformly at every coordinate above the moving
`sourceSigma` endpoint.  The proof keeps `s` free: the logarithmic loss is
transported with `u = s / sourceSigma`, while the `s^d / log D` gain supplies
`d * log u`. -/
theorem claim145_sourceSigma_allS_scalar_eventually
    (S : BoundingSieve) {d Δ K C C145 M : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ᶠ D : ℝ in atTop, ∀ s : ℝ, sourceSigma D d ≤ s →
      0 < sourceSigma D d ∧ M ≤ s ∧
      Real.exp 1 * suzukiSourceL D K ≤ s - 2 ∧
      Real.exp
          (suzukiSourceL D K +
            (s - 2) *
              (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2))) ≤
        C145 *
          (claim14_5VProduct S D *
            (Real.exp (Real.sqrt K) /
              (Real.log D * sourceSigma D d)) *
            ((1 + s ^ d / Real.log D) ^ s * s *
              proposition131iiLowerProfile C s) *
            (Real.log D) ^ (-Δ)) := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd7 : 7 < d := by
    have hfrac : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hβ]
      nlinarith
    exact hfrac.trans_lt hd
  have hd0 : 0 < d := by linarith
  -- Choose eventual thresholds using logarithmic growth versus `x^(1/d)`.
  let a : ℝ := 1 / d
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ d by linarith)
    simpa using h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := -Real.log (Real.log 2) + Real.log (1 + K / Real.log 2)
  let A : ℝ := (1 / Real.log 2) * (1 + K / Real.log 2)
  have hA : 0 < A := by dsimp [A]; positivity
  /- Keep the auxiliary comparison constant free of `exp (sqrt K)`.  That
  favourable factor belongs on the final Claim-14.5 side; inserting it into
  `Q` would make the elementary threshold below grow like `sqrt K` and would
  destroy the source-uniform `C1 * K^Theta < log D` quantifier. -/
  let Q : ℝ := C145 / A
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hdom0 := (isLittleO_log_rpow_rpow_atTop 2 ha).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hdom : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x) ^ 2 ≤ x ^ a := by
    filter_upwards [hdom0, eventually_ge_atTop (1 : ℝ)] with x hxdom hx1
    have hxpow : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) _
    rw [Real.rpow_two] at hxdom
    change |(Real.log x) ^ 2| ≤ 1 / 2 * |x ^ a| at hxdom
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hxpow] at hxdom
    nlinarith
  obtain ⟨X, hX⟩ := (eventually_atTop.1 hdom)
  let q0 : ℝ := max 6 (max (|B| + 2)
    (max (9 + |Real.log Q|) (Real.exp 1 + 2)))
  let r0 : ℝ := (C + 2 + Real.log 2) / (d - 4)
  have hloglog : Tendsto (fun D : ℝ => Real.log (Real.log D)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlogloglog :
      Tendsto (fun D : ℝ => Real.log (Real.log (Real.log D))) atTop atTop :=
    Real.tendsto_log_atTop.comp hloglog
  filter_upwards [eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (max X (max 2 (Real.log 27))),
      hloglog.eventually_ge_atTop q0,
      hloglog.eventually_ge_atTop (max M 0),
      hlogloglog.eventually_ge_atTop r0] with D hD1 hxlarge hqlarge hqM hrlarge
  intro s hsσ
  -- Normalize the endpoint: `x = log D`, `q = log x`, and `σ = x^a * ell`.
  let x : ℝ := Real.log D
  let q : ℝ := Real.log x
  let ell : ℝ := Real.log (Real.log (27 * D))
  let σ : ℝ := sourceSigma D d
  let L : ℝ := suzukiSourceL D K
  let u : ℝ := s / σ
  let b : ℝ := 1 + s ^ d / x
  have hD2 : 2 ≤ D := hD1
  have hDpos : 0 < D := by linarith
  have hxX : X ≤ x := by
    dsimp [x]
    exact (le_max_left X (max 2 (Real.log 27))).trans hxlarge
  have hxrest : max 2 (Real.log 27) ≤ x := by
    dsimp [x]
    exact (le_max_right X (max 2 (Real.log 27))).trans hxlarge
  have hx2 : 2 ≤ x := (le_max_left 2 (Real.log 27)).trans hxrest
  have hx27 : Real.log 27 ≤ x := (le_max_right 2 (Real.log 27)).trans hxrest
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq4 : 4 ≤ q := by
    dsimp [q, x]
    exact (show (4 : ℝ) ≤ 6 by norm_num).trans ((le_max_left _ _).trans hqlarge)
  have hq : 0 < q := by linarith
  have hqB : |B| + 2 ≤ q := by
    dsimp [q, x]
    exact (le_max_left (|B| + 2) _).trans
      ((le_max_right 6 _).trans hqlarge)
  have hqQ : 9 + |Real.log Q| ≤ q := by
    dsimp [q, x]
    exact (le_max_left (9 + |Real.log Q|) _).trans
      ((le_max_right (|B| + 2) _).trans ((le_max_right 6 _).trans hqlarge))
  have hqe : Real.exp 1 + 2 ≤ q := by
    dsimp [q, x]
    exact (le_max_right (9 + |Real.log Q|) _).trans
      ((le_max_right (|B| + 2) _).trans ((le_max_right 6 _).trans hqlarge))
  have hMq : M ≤ q := by
    dsimp [q, x]
    exact (le_max_left M 0).trans hqM
  have hr : r0 ≤ Real.log q := by simpa [r0, q, x] using hrlarge
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    dsimp [x]
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinnerLower : x ≤ Real.log (27 * D) := by
    rw [hlog27D]
    exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
  have hinnerUpper : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinnerPos : 0 < Real.log (27 * D) := hx.trans_le hinnerLower
  have hellLower : q ≤ ell := by
    dsimp [q, ell]
    exact Real.log_le_log hx hinnerLower
  have hellUpper : ell ≤ 2 * q := by
    have h := Real.log_le_log hinnerPos hinnerUpper
    have hlog2leq : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    dsimp [q] at hlog2leq
    dsimp [ell, q]
    linarith
  have hell : 0 < ell := hq.trans_le hellLower
  have hxa1 : 1 ≤ x ^ a := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      hx1 ha.le
  have hxale : x ^ a ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 ha1
  have hσdef : σ = x ^ a * ell := by rfl
  have hσLower : x ^ a * q ≤ σ := by
    rw [hσdef]
    exact mul_le_mul_of_nonneg_left hellLower (Real.rpow_nonneg hx.le _)
  have hσUpper : σ ≤ 2 * x * q := by
    rw [hσdef]
    calc
      x ^ a * ell ≤ x * (2 * q) := mul_le_mul hxale hellUpper hell.le hx.le
      _ = 2 * x * q := by ring
  have hσ4 : 4 ≤ σ := by
    calc 4 ≤ q := hq4
      _ ≤ x ^ a * q := le_mul_of_one_le_left hq.le hxa1
      _ ≤ σ := hσLower
  have hσpos : 0 < σ := by linarith
  have hsσ' : σ ≤ s := by simpa [σ] using hsσ
  have hs4 : 4 ≤ s := hσ4.trans hsσ'
  have hspos : 0 < s := by linarith
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact (le_div_iff₀ hσpos).2 (by simpa using hsσ')
  have hupos : 0 < u := zero_lt_one.trans_le hu1
  have hsu : s = σ * u := by
    dsimp [u]
    field_simp [ne_of_gt hσpos]
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hlogu_le : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
  have hlogsSplit : Real.log s = Real.log σ + Real.log u := by
    rw [hsu, Real.log_mul (ne_of_gt hσpos) (ne_of_gt hupos)]
  have hLdef : L = q + B := by
    dsimp [L, q, x, B, suzukiSourceL]
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hlog2)]
    ring
  have hL : 1 ≤ L := by
    rw [hLdef]
    have hnegB : -|B| ≤ B := neg_abs_le B
    linarith
  have hLsq : L ≤ q ^ 2 := by
    rw [hLdef]
    have hBabs : B ≤ |B| := le_abs_self B
    nlinarith only [hqB, hBabs, sq_nonneg (q - 1)]
  have hdomx : 2 * q ^ 2 ≤ x ^ a := by
    simpa [q] using hX x hxX
  have habsorbσ : q ^ 2 + 9 * q + |Real.log Q| ≤ σ := by
    have htail : 9 * q + |Real.log Q| ≤ q ^ 2 := by
      have habs : 0 ≤ |Real.log Q| := abs_nonneg _
      nlinarith only [hqQ, hq4, habs]
    have hxa_le_σ : x ^ a ≤ σ := by
      calc
        x ^ a ≤ x ^ a * q :=
          le_mul_of_one_le_right (Real.rpow_nonneg hx.le a) (by linarith only [hq4])
        _ ≤ σ := hσLower
    calc
      q ^ 2 + 9 * q + |Real.log Q| ≤ 2 * q ^ 2 := by linarith only [htail]
      _ ≤ x ^ a := hdomx
      _ ≤ σ := hxa_le_σ
  have hsourceσ : Real.exp 1 * L ≤ σ - 2 := by
    have hsigStrong : Real.exp 1 * q ^ 2 + 2 ≤ 2 * q ^ 3 := by
      have hepos := Real.exp_pos 1
      nlinarith only [hq4, hepos, sq_nonneg q,
        mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hqe)]
    have htwoq3 : 2 * q ^ 3 ≤ σ := by
      have hmul := mul_le_mul_of_nonneg_right hdomx hq.le
      calc
        2 * q ^ 3 = (2 * q ^ 2) * q := by ring
        _ ≤ x ^ a * q := hmul
        _ ≤ σ := hσLower
    linarith only [hsigStrong, htwoq3,
      mul_le_mul_of_nonneg_left hLsq (Real.exp_pos 1).le]
  have hsource : Real.exp 1 * L ≤ s - 2 := by linarith only [hsourceσ, hsσ']
  have hlogsσ : Real.log σ ≤ 3 * q := by
    have hboundpos : 0 < 2 * x * q := by positivity
    have h := Real.log_le_log hσpos hσUpper
    rw [Real.log_mul (by positivity : (2 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    have hlog2le : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (sub_le_self q zero_le_one)
    dsimp [q] at hlog2le
    linarith
  have hloglog3σ : Real.log (Real.log (3 * σ)) ≤ 2 * Real.log q := by
    have h3σ : 0 < 3 * σ := by positivity
    have h6xq : 3 * σ ≤ 6 * x * q := by linarith only [hσUpper]
    have h6pos : 0 < 6 * x * q := by positivity
    have hlogfirst := Real.log_le_log h3σ h6xq
    rw [Real.log_mul (by positivity : (6 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hx)] at hlogfirst
    have hlog6le : Real.log 6 ≤ q := by
      have hq6 : (6 : ℝ) ≤ q := by
        dsimp [q, x]
        exact (le_max_left _ _).trans hqlarge
      exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)).trans (by linarith)
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (sub_le_self q zero_le_one)
    have hinner : Real.log (3 * σ) ≤ 3 * q := by
      dsimp [q] at hlog6le
      linarith
    have hinnerpos : 0 < Real.log (3 * σ) := Real.log_pos (by linarith only [hσ4])
    have h3qpos : 0 < 3 * q := by positivity
    have hsecond := Real.log_le_log hinnerpos hinner
    have hlog3le : Real.log 3 ≤ Real.log q :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hq (by linarith : (3 : ℝ) ≤ q)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hq)] at hsecond
    linarith
  have hlogL : Real.log L ≤ 2 * Real.log q := by
    have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hq
    have h := Real.log_le_log (by linarith : 0 < L) hLsq
    rw [Real.log_pow] at h
    simpa using h
  have hconst : C + 2 + Real.log 2 ≤ (d - 4) * Real.log q := by
    have hd4 : 0 < d - 4 := by linarith
    have ht := mul_le_mul_of_nonneg_left hr hd4.le
    dsimp [r0] at ht
    field_simp [ne_of_gt hd4] at ht
    linarith
  -- Transport the endpoint bounds to every `s ≥ σ` using `u = s / σ ≥ 1`.
  have habsorb : L + 2 * Real.log s + 3 * q + |Real.log Q| ≤ s := by
    have hbase : L + 2 * Real.log σ + 3 * q + |Real.log Q| ≤ σ := by
      linarith only [hLsq, hlogsσ, habsorbσ]
    rw [hlogsSplit]
    have hlogtransport : 2 * Real.log u ≤ 2 * (u - 1) :=
      mul_le_mul_of_nonneg_left hlogu_le (by norm_num)
    have hscale : 2 * (u - 1) ≤ σ * (u - 1) :=
      mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ σ)
        (sub_nonneg.mpr hu1)
    have htransport : 2 * Real.log u ≤ s - σ := by
      calc
        2 * Real.log u ≤ 2 * (u - 1) := hlogtransport
        _ ≤ σ * (u - 1) := hscale
        _ = s - σ := by rw [hsu]; ring
    linarith only [hbase, htransport]
  have hqσ : q ≤ σ := by
    have hm := mul_le_mul_of_nonneg_right hxa1 hq.le
    have hm' : q ≤ x ^ a * q := by simpa [mul_comm] using hm
    exact hm'.trans hσLower
  have hAlog : 1 ≤ Real.log (3 * σ) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 3 * σ)).2
    calc
      Real.exp 1 ≤ q := by linarith [hqe]
      _ ≤ σ := hqσ
      _ ≤ 3 * σ := by linarith [hσpos]
  have hlog3s_mul : Real.log (3 * s) =
      Real.log (3 * σ) + Real.log u := by
    rw [hsu]
    rw [show 3 * (σ * u) = (3 * σ) * u by ring,
      Real.log_mul (by positivity : (3 * σ : ℝ) ≠ 0) (ne_of_gt hupos)]
  have hlog3s_le : Real.log (3 * s) ≤ u * Real.log (3 * σ) := by
    rw [hlog3s_mul]
    calc
      Real.log (3 * σ) + Real.log u ≤ Real.log (3 * σ) + (u - 1) :=
        by simpa [add_comm] using add_le_add_left hlogu_le (Real.log (3 * σ))
      _ ≤ Real.log (3 * σ) + (u - 1) * Real.log (3 * σ) := by
        have hm := mul_le_mul_of_nonneg_left hAlog (sub_nonneg.mpr hu1)
        simpa using hm
      _ = u * Real.log (3 * σ) := by ring
  have hloglog3s :
      Real.log (Real.log (3 * s)) ≤ 2 * Real.log q + Real.log u := by
    have hleftpos : 0 < Real.log (3 * s) := Real.log_pos (by linarith only [hs4])
    have hrightpos : 0 < u * Real.log (3 * σ) := mul_pos hupos (lt_of_lt_of_le zero_lt_one hAlog)
    have hh := Real.log_le_log hleftpos hlog3s_le
    rw [Real.log_mul (ne_of_gt hupos)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hAlog))] at hh
    linarith
  -- The gain `s^d / log D` dominates the logarithmic losses.
  have hσPow : σ ^ d = x * ell ^ d := by
    rw [hσdef, Real.mul_rpow (Real.rpow_nonneg hx.le _) hell.le]
    have hxad : (x ^ a) ^ d = x := by
      rw [← Real.rpow_mul hx.le]
      have : a * d = 1 := by dsimp [a]; field_simp
      rw [this, Real.rpow_one]
    rw [hxad]
  have hsPow : s ^ d = u ^ d * (x * ell ^ d) := by
    rw [hsu, Real.mul_rpow hσpos.le hupos.le, hσPow]
    ring
  have hquot : s ^ d / x = u ^ d * ell ^ d := by
    rw [hsPow]
    field_simp [ne_of_gt hx]
  have hbpos : 0 < b := by
    dsimp [b]
    have : 0 ≤ s ^ d / x := div_nonneg (Real.rpow_nonneg hspos.le _) hx.le
    linarith
  have hblog : d * Real.log q + d * Real.log u ≤ Real.log b := by
    have hqpow : q ^ d ≤ ell ^ d := Real.rpow_le_rpow hq.le hellLower hd0.le
    have hupow : 0 ≤ u ^ d := Real.rpow_nonneg hupos.le _
    have hy_le : u ^ d * q ^ d ≤ b := by
      dsimp [b]
      rw [hquot]
      exact (mul_le_mul_of_nonneg_left hqpow hupow).trans
        (le_add_of_nonneg_left zero_le_one)
    have hypos : 0 < u ^ d * q ^ d := mul_pos (Real.rpow_pos_of_pos hupos _)
      (Real.rpow_pos_of_pos hq _)
    have hh := Real.log_le_log hypos hy_le
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hupos _))
      (ne_of_gt (Real.rpow_pos_of_pos hq _)),
      Real.log_rpow hupos d, Real.log_rpow hq d] at hh
    linarith
  have hgap : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
      Real.log b := by
    have hmid : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
        d * Real.log q + d * Real.log u := by
      nlinarith only [hlogL, hloglog3s, hconst,
        mul_nonneg (show 0 ≤ d - 1 by linarith only [hd7]) hlogu0]
    exact hmid.trans hblog
  -- Combine the scalar exponent comparison with the sieve-product lower bound.
  have hcore := claim145_caseB_scalar_exponent_comparison hx hq hL hs4 hQ rfl
    habsorb hgap
  have hVedge := claim14_5VProduct_lower_of_localProduct
    (S := S) (D := D) (K := K) hD2 hlocal
  have hAform : (Real.log D / Real.log 2) * (1 + K / Real.log 2) = A * x := by
    dsimp [A, x]
    ring
  rw [hAform] at hVedge
  have hpowDelta : x ^ (-1 : ℝ) ≤ x ^ (-Δ) := by
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpref : Q / x ^ 3 ≤
      C145 * (claim14_5VProduct S D *
        (Real.exp (Real.sqrt K) / x)) * x ^ (-Δ) := by
    have hnonneg : 0 ≤ Q / x ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hVedge hnonneg
    have hVpos : 0 < claim14_5VProduct S D := by
      unfold claim14_5VProduct
      apply Finset.prod_pos
      intro p hp
      have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
      have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
      exact sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv)
    calc
      Q / x ^ 3 ≤ (claim14_5VProduct S D * (A * x)) * (Q / x ^ 3) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      _ = C145 * (claim14_5VProduct S D * (1 / x)) *
          x ^ (-1 : ℝ) := by
            dsimp [Q]
            rw [Real.rpow_neg_one]
            field_simp [ne_of_gt hx, ne_of_gt hA]
      _ ≤ C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-1 : ℝ) := by
            have hexpK : 1 ≤ Real.exp (Real.sqrt K) :=
              Real.one_le_exp (Real.sqrt_nonneg K)
            gcongr
      _ ≤ C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) := by gcongr
  have hscalarCore :
      Real.exp (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
        C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) *
          Real.exp (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s) := by
    exact hcore.trans (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le)
  have hprofile :
      b ^ s * proposition131iiLowerProfile C s =
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
    unfold proposition131iiLowerProfile
    rw [Real.rpow_def_of_pos hbpos, ← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [σ] using hσpos
  · exact hMq.trans (hqσ.trans hsσ')
  · simpa [L] using hsource
  · rw [← hprofile] at hscalarCore
    have hVnonneg : 0 ≤ claim14_5VProduct S D := by
      unfold claim14_5VProduct
      apply Finset.prod_nonneg
      intro p hp
      have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
      have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
      exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
    have hprofnonneg : 0 ≤ proposition131iiLowerProfile C s := by
      unfold proposition131iiLowerProfile
      exact (Real.exp_pos _).le
    have hbpow : 0 ≤ b ^ s := Real.rpow_nonneg hbpos.le _
    have holdnonneg : 0 ≤
        C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s) := by
      positivity
    have hratio : 1 ≤ s / σ := by
      apply (le_div_iff₀ hσpos).2
      simpa using hsσ'
    have hlift :
        C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s) ≤
          C145 * (claim14_5VProduct S D *
            (Real.exp (Real.sqrt K) / (x * σ))) *
            (b ^ s * s * proposition131iiLowerProfile C s) * x ^ (-Δ) := by
      calc
        _ = (C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s)) * 1 := by ring
        _ ≤ (C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s)) * (s / σ) :=
          mul_le_mul_of_nonneg_left hratio holdnonneg
        _ = _ := by field_simp [ne_of_gt hx, ne_of_gt hσpos]
    have hdesired := hscalarCore.trans hlift
    simpa only [σ, L, b, x, mul_assoc] using hdesired


end MathlibNt.SieveTheory
