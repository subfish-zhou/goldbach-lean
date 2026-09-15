import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ComparisonInternal

open scoped Classical BigOperators
open Filter Finset Topology
open Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The dimension-one local-product contract gives the needed lower edge for
Claim 14.5's finite Euler product. -/
theorem claim14_5VProduct_lower_of_localProduct
    {S : BoundingSieve} {D K : ℝ} (hD : 2 ≤ D)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    1 ≤ claim14_5VProduct S D *
      ((Real.log D / Real.log 2) * (1 + K / Real.log 2)) := by
  have hraw := hlocal 2 D (by norm_num) hD
  have hsets :
      S.prodPrimes.primeFactors.filter
          (fun p : ℕ => (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < D) =
        S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < D) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, _hp2, hpD⟩
      exact ⟨hp, hpD⟩
    · rintro ⟨hp, hpD⟩
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact ⟨hp, by exact_mod_cast hpprime.two_le, hpD⟩
  have hrewrite : suzukiLocalRatio S 2 D =
      (claim14_5VProduct S D)⁻¹ := by
    unfold suzukiLocalRatio claim14_5VProduct
    rw [hsets, Finset.prod_inv_distrib]
  have hraw' : (claim14_5VProduct S D)⁻¹ ≤
      (Real.log D / Real.log 2) * (1 + K / Real.log 2) := by
    rw [← hrewrite]
    exact hlocal 2 D (by norm_num) hD
  have hVpos : 0 < claim14_5VProduct S D := by
    unfold claim14_5VProduct
    apply Finset.prod_pos
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
    exact sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv)
  have hmul := mul_le_mul_of_nonneg_left hraw' hVpos.le
  rw [mul_inv_cancel₀ (ne_of_gt hVpos)] at hmul
  simpa [mul_assoc] using hmul

/-- Elementary logarithmic comparison used after all moving quantities have
been bounded.  It keeps the decisive negative `-s log s` term on both sides. -/
theorem claim145_scalar_exponent_comparison
    {x q L s b C Q : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hL : 1 ≤ L) (hs : 4 ≤ s)
    (hQ : 0 < Q) (hqlog : q = Real.log x)
    (hLsq : L ≤ q ^ 2) (hlogs : Real.log s ≤ 3 * q)
    (habsorb : q ^ 2 + 9 * q + |Real.log Q| ≤ s)
    (hgap : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
      Real.log b) :
    Real.exp
        (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
      Q / x ^ 3 *
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
  have hs0 : 0 < s := by linarith
  have hs2 : 0 < s - 2 := by linarith
  have hsHalf : s / 2 ≤ s - 2 := by linarith
  have hlogHalf : Real.log s - Real.log 2 ≤ Real.log (s - 2) := by
    rw [← Real.log_div (ne_of_gt hs0) (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) hsHalf
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hleft :
      L + (s - 2) * (1 + Real.log L - Real.log (s - 2)) ≤
        L + s * (1 + Real.log L - Real.log s + Real.log 2) +
          2 * Real.log s := by
    have hmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hlogHalf (1 + Real.log L)) (sub_nonneg.mpr (by linarith : 2 ≤ s))
    nlinarith
  have hmain :
      L + s * (1 + Real.log L - Real.log s + Real.log 2) +
          2 * Real.log s + 3 * q - Real.log Q ≤
        s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s := by
    have hgap' := mul_le_mul_of_nonneg_left hgap (show 0 ≤ s by linarith)
    have hlogQ : -Real.log Q ≤ |Real.log Q| := neg_le_abs _
    nlinarith
  have hexp :
      Real.exp
          (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
        Real.exp
          (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s - 3 * q + Real.log Q) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s - 3 * q + Real.log Q) := hexp
    _ = Q / x ^ 3 *
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
      rw [Real.exp_add, Real.exp_log hQ]
      rw [show s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s - 3 * q =
          -3 * q + (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s) by ring]
      rw [Real.exp_add]
      rw [hqlog]
      rw [show -3 * Real.log x = -Real.log x + (-Real.log x + -Real.log x) by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hx]
      field_simp

/-- The scalar comparison in the literal Case-B variables.  Unlike the endpoint
specialization above, the harmless terms are absorbed directly at the actual
coordinate `s`; this is what permits every `s ≥ sourceSigma D d`. -/
theorem claim145_caseB_scalar_exponent_comparison
    {x q L s b C Q : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hL : 1 ≤ L) (hs : 4 ≤ s)
    (hQ : 0 < Q) (hqlog : q = Real.log x)
    (habsorb : L + 2 * Real.log s + 3 * q + |Real.log Q| ≤ s)
    (hgap : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
      Real.log b) :
    Real.exp
        (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
      Q / x ^ 3 *
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
  have hs0 : 0 < s := by linarith
  have hsHalf : s / 2 ≤ s - 2 := by linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogHalf : Real.log s - Real.log 2 ≤ Real.log (s - 2) := by
    rw [← Real.log_div (ne_of_gt hs0) (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) hsHalf
  have hleft :
      L + (s - 2) * (1 + Real.log L - Real.log (s - 2)) ≤
        L + s * (1 + Real.log L - Real.log s + Real.log 2) +
          2 * Real.log s := by
    have hmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hlogHalf (1 + Real.log L))
      (sub_nonneg.mpr (by linarith : 2 ≤ s))
    nlinarith
  have hmain :
      L + s * (1 + Real.log L - Real.log s + Real.log 2) +
          2 * Real.log s + 3 * q - Real.log Q ≤
        s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s := by
    have hgap' := mul_le_mul_of_nonneg_left hgap (show 0 ≤ s by linarith)
    have hlogQ : -Real.log Q ≤ |Real.log Q| := neg_le_abs _
    nlinarith
  have hexp :
      Real.exp
          (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
        Real.exp
          (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s - 3 * q + Real.log Q) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s - 3 * q + Real.log Q) := hexp
    _ = Q / x ^ 3 *
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
      rw [Real.exp_add, Real.exp_log hQ]
      rw [show s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s - 3 * q =
          -3 * q + (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s) by ring]
      rw [Real.exp_add, hqlog]
      rw [show -3 * Real.log x = -Real.log x + (-Real.log x + -Real.log x) by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hx]
      field_simp

/-- At Suzuki's exact moving endpoint, both analytic premises required by the
internal Claim-14.5 comparison hold eventually. -/
theorem claim145_sourceSigma_scalar_eventually
    (S : BoundingSieve) {d Δ K C C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ᶠ D : ℝ in atTop,
      Real.exp 1 * suzukiSourceL D K ≤ sourceSigma D d - 2 ∧
      Real.exp
          (suzukiSourceL D K +
            (sourceSigma D d - 2) *
              (1 + Real.log (suzukiSourceL D K) -
                Real.log (sourceSigma D d - 2))) ≤
        C145 *
          (claim14_5VProduct S D *
            (Real.exp (Real.sqrt K) /
              (Real.log D * sourceSigma D d)) *
            ((1 + (sourceSigma D d) ^ d / Real.log D) ^
                (sourceSigma D d) * sourceSigma D d *
              proposition131iiLowerProfile C (sourceSigma D d)) *
            (Real.log D) ^ (-Δ)) := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd7 : 7 < d := by
    have hfrac : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hβ]
      nlinarith
    exact hfrac.trans_lt hd
  have hd0 : 0 < d := by linarith
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
  let Q : ℝ := C145 * Real.exp (Real.sqrt K) / A
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
      hlogloglog.eventually_ge_atTop r0] with D hD1 hxlarge hqlarge hrlarge
  let x : ℝ := Real.log D
  let q : ℝ := Real.log x
  let ell : ℝ := Real.log (Real.log (27 * D))
  let s : ℝ := sourceSigma D d
  let L : ℝ := suzukiSourceL D K
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
  have hsdef : s = x ^ a * ell := by rfl
  have hsLower : x ^ a * q ≤ s := by
    rw [hsdef]
    exact mul_le_mul_of_nonneg_left hellLower (Real.rpow_nonneg hx.le _)
  have hsUpper : s ≤ 2 * x * q := by
    rw [hsdef]
    nlinarith [mul_le_mul hxale hellUpper hell.le hx.le]
  have hs4 : 4 ≤ s := by
    calc 4 ≤ q := hq4
      _ ≤ x ^ a * q := by nlinarith
      _ ≤ s := hsLower
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
    nlinarith [sq_nonneg (q - 2)]
  have hdomx : 2 * q ^ 2 ≤ x ^ a := by
    simpa [q] using hX x hxX
  have habsorb : q ^ 2 + 9 * q + |Real.log Q| ≤ s := by
    have htail : 9 * q + |Real.log Q| ≤ q ^ 2 := by
      have habs : 0 ≤ |Real.log Q| := abs_nonneg _
      nlinarith
    have hxa_le_s : x ^ a ≤ s := by
      calc x ^ a ≤ x ^ a * q := by nlinarith [Real.rpow_nonneg hx.le a]
        _ ≤ s := hsLower
    linarith
  have hsource : Real.exp 1 * L ≤ s - 2 := by
    have hsigStrong : Real.exp 1 * q ^ 2 + 2 ≤ 2 * q ^ 3 := by
      have hepos := Real.exp_pos 1
      nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hqe)]
    have htwoq3 : 2 * q ^ 3 ≤ s := by
      have hmul := mul_le_mul_of_nonneg_right hdomx hq.le
      calc
        2 * q ^ 3 = (2 * q ^ 2) * q := by ring
        _ ≤ x ^ a * q := hmul
        _ ≤ s := hsLower
    nlinarith [mul_le_mul_of_nonneg_left hLsq (Real.exp_pos 1).le]
  have hlogs : Real.log s ≤ 3 * q := by
    have hspos : 0 < s := by linarith
    have hsx : s ≤ 2 * x * q := hsUpper
    have hboundpos : 0 < 2 * x * q := by positivity
    have h := Real.log_le_log hspos hsx
    rw [Real.log_mul (by positivity : (2 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    have hlog2le : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
    dsimp [q] at hlog2le
    linarith
  have hloglog3s : Real.log (Real.log (3 * s)) ≤ 2 * Real.log q := by
    have hspos : 0 < s := by linarith
    have h3s : 0 < 3 * s := by positivity
    have h6xq : 3 * s ≤ 6 * x * q := by nlinarith [hsUpper]
    have h6pos : 0 < 6 * x * q := by positivity
    have hlogfirst := Real.log_le_log h3s h6xq
    rw [Real.log_mul (by positivity : (6 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hx)] at hlogfirst
    have hlog6le : Real.log 6 ≤ q := by
      have hq6 : (6 : ℝ) ≤ q := by
        dsimp [q, x]
        exact (le_max_left _ _).trans hqlarge
      exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)).trans (by linarith)
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
    have hinner : Real.log (3 * s) ≤ 3 * q := by
      dsimp [q] at hlog6le
      linarith
    have hinnerpos : 0 < Real.log (3 * s) := Real.log_pos (by nlinarith [hs4])
    have h3qpos : 0 < 3 * q := by positivity
    have hsecond := Real.log_le_log hinnerpos hinner
    have hlog3le : Real.log 3 ≤ Real.log q :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hq (by linarith : (3 : ℝ) ≤ q)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hq)] at hsecond
    linarith
  have hsPow : s ^ d = x * ell ^ d := by
    rw [hsdef, Real.mul_rpow (Real.rpow_nonneg hx.le _) hell.le]
    have hxad : (x ^ a) ^ d = x := by
      rw [← Real.rpow_mul hx.le]
      have : a * d = 1 := by dsimp [a]; field_simp
      rw [this, Real.rpow_one]
    rw [hxad]
  have hbdef : b = 1 + ell ^ d := by
    dsimp [b]
    rw [hsPow]
    field_simp [ne_of_gt hx]
  have hbpos : 0 < b := by rw [hbdef]; positivity
  have hlogbase : d * Real.log q ≤ Real.log b := by
    have hellpowpos : 0 < ell ^ d := Real.rpow_pos_of_pos hell _
    have hpowle : ell ^ d ≤ b := by rw [hbdef]; linarith
    have hlogpow := Real.log_le_log hellpowpos hpowle
    rw [Real.log_rpow hell d] at hlogpow
    have hlogqell := Real.log_le_log hq hellLower
    nlinarith [mul_le_mul_of_nonneg_left hlogqell hd0.le]
  have hlogL : Real.log L ≤ 2 * Real.log q := by
    have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hq
    have h := Real.log_le_log (by linarith : 0 < L) hLsq
    rw [Real.log_pow] at h
    simpa using h
  have hgap : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
      Real.log b := by
    have hd4 : 0 < d - 4 := by linarith
    have hconst : C + 2 + Real.log 2 ≤ (d - 4) * Real.log q := by
      have := mul_le_mul_of_nonneg_left hr hd4.le
      dsimp [r0] at this
      field_simp [ne_of_gt hd4] at this
      linarith
    linarith
  have hcore := claim145_scalar_exponent_comparison hx hq hL hs4 hQ rfl
    hLsq hlogs habsorb hgap
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
      _ = C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-1 : ℝ) := by
            dsimp [Q]
            rw [Real.rpow_neg_one]
            field_simp [ne_of_gt hx, ne_of_gt hA]
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
  refine ⟨?_, ?_⟩
  · simpa [s, L] using hsource
  · rw [← hprofile] at hscalarCore
    have hdesired :
        Real.exp (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
          C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / (x * s))) *
            (b ^ s * s * proposition131iiLowerProfile C s) * x ^ (-Δ) := by
      calc
        _ ≤ C145 * (claim14_5VProduct S D * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s) := hscalarCore
        _ = _ := by
          field_simp [ne_of_gt (show 0 < s by linarith)]
    simpa only [s, L, b, x, mul_assoc] using hdesired


end MathlibNt.SieveTheory
