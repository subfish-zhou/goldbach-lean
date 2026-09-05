import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseALowS
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ScalarEventual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceBranchInterface

open scoped Classical BigOperators
open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-!
# Claim 14.5, Case A, high-`s`: actual closure

This file closes the source-small-`D`, high-coordinate branch directly for the
actual discrete quantity.  The final statement is uniform in the natural depth
`N`, in every natural `D ≥ 2` satisfying `log D ≤ C₁ K^Θ`, and in every real
`s ≥ √K / log K`.  No residual scalar comparison premise remains.
-/

theorem claim145_caseA_highS_sourceL_le_logK
    {D K C1 Θ : ℝ}
    (hD : 2 ≤ D) (hK : 3 ≤ K) (hlogK1 : 1 ≤ Real.log K)
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hsmall : Real.log D ≤ C1 * K ^ Θ) :
    suzukiSourceL D K ≤
      (Θ + 2 + |Real.log C1| + |Real.log (Real.log 2)|) * Real.log K := by
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := by linarith
  have hK0 : 0 < K := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hKpow : 0 < K ^ Θ := Real.rpow_pos_of_pos hK0 _
  have hloglogD : Real.log (Real.log D) ≤ Real.log C1 + Θ * Real.log K := by
    have hh := Real.log_le_log hlogD hsmall
    rw [Real.log_mul (ne_of_gt hC1) (ne_of_gt hKpow), Real.log_rpow hK0 Θ] at hh
    exact hh
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbaseK : 1 + K / Real.log 2 ≤ K ^ 2 := by
    have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hpart : K / Real.log 2 ≤ 2 * K := by
      apply (div_le_iff₀ hlog2).2
      nlinarith
    nlinarith [sq_nonneg (K - 3)]
  have hlogbase : Real.log (1 + K / Real.log 2) ≤ 2 * Real.log K := by
    have hbpos : 0 < 1 + K / Real.log 2 := by positivity
    have hh := Real.log_le_log hbpos hbaseK
    rw [Real.log_pow] at hh
    simpa using hh
  have hlogC1 : Real.log C1 ≤ |Real.log C1| * Real.log K := by
    calc
      Real.log C1 ≤ |Real.log C1| := le_abs_self _
      _ ≤ |Real.log C1| * Real.log K := by
        nlinarith [abs_nonneg (Real.log C1)]
  have hloglog2 : -Real.log (Real.log 2) ≤
      |Real.log (Real.log 2)| * Real.log K := by
    calc
      -Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := neg_le_abs _
      _ ≤ |Real.log (Real.log 2)| * Real.log K := by
        nlinarith [abs_nonneg (Real.log (Real.log 2))]
  unfold suzukiSourceL
  rw [Real.log_div (ne_of_gt hlogD) (ne_of_gt hlog2)]
  nlinarith

theorem claim145_caseA_highS_sourceSigma_le_Kbound
    {D K C1 Θ d : ℝ}
    (hD : 2 ≤ D) (hK : 3 ≤ K) (hlogK1 : 1 ≤ Real.log K)
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ) (hd : 0 < d)
    (hsmall : Real.log D ≤ C1 * K ^ Θ) :
    sourceSigma D d ≤
      (C1 ^ (1 / d)) *
        (Θ + |Real.log C1| + |Real.log (Real.log 2)| + |Real.log (Real.log 27 / Real.log 2 + 1)|)
        * K ^ (Θ / d) * Real.log K := by
  let R : ℝ := Real.log 27 / Real.log 2 + 1
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := by linarith
  have hK0 : 0 < K := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hKpow : 0 < K ^ Θ := Real.rpow_pos_of_pos hK0 _
  have hC1pow : 0 < C1 ^ (1 / d) := Real.rpow_pos_of_pos hC1 _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR0 : 0 < R := by
    dsimp [R]
    positivity
  have hpow : (Real.log D) ^ (1 / d) ≤ (C1 * K ^ Θ) ^ (1 / d) := by
    exact Real.rpow_le_rpow hlogD.le hsmall (by positivity : 0 ≤ 1 / d)
  have hpow' : (Real.log D) ^ (1 / d) ≤ C1 ^ (1 / d) * K ^ (Θ / d) := by
    calc
      (Real.log D) ^ (1 / d) ≤ (C1 * K ^ Θ) ^ (1 / d) := hpow
      _ = C1 ^ (1 / d) * K ^ (Θ / d) := by
        rw [Real.mul_rpow hC1.le (Real.rpow_nonneg hK0.le _),
          ← Real.rpow_mul hK0.le]
        congr 2
        field_simp [hd.ne']
  have hlog27D_eq : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hD0)]
  have hlogD2 : Real.log 2 ≤ Real.log D :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hD0 hD
  have hlog27D_bound : Real.log (27 * D) ≤ R * Real.log D := by
    rw [hlog27D_eq]
    have hc : 0 ≤ Real.log 27 / Real.log 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hlogD2 hc
    dsimp [R]
    calc
      Real.log 27 + Real.log D =
          (Real.log 27 / Real.log 2) * Real.log 2 + Real.log D := by
            field_simp
      _ ≤ (Real.log 27 / Real.log 2) * Real.log D + Real.log D := by
        simpa [add_comm] using add_le_add_right hh (Real.log D)
      _ = (Real.log 27 / Real.log 2 + 1) * Real.log D := by ring
  have hlog27D_one : 1 < Real.log (27 * D) := by
    rw [Real.lt_log_iff_exp_lt (by positivity : 0 < 27 * D)]
    nlinarith [Real.exp_one_lt_three]
  have hlog27D : 0 < Real.log (27 * D) := zero_lt_one.trans hlog27D_one
  have hll : Real.log (Real.log (27 * D)) ≤
      Real.log R + Real.log (Real.log D) := by
    have hh := Real.log_le_log hlog27D hlog27D_bound
    rw [Real.log_mul (ne_of_gt hR0) (ne_of_gt hlogD)] at hh
    exact hh
  have hloglogD : Real.log (Real.log D) ≤ Real.log C1 + Θ * Real.log K := by
    have hh := Real.log_le_log hlogD hsmall
    rw [Real.log_mul (ne_of_gt hC1) (ne_of_gt hKpow), Real.log_rpow hK0 Θ] at hh
    exact hh
  have hlogterm :
      Real.log (Real.log (27 * D)) ≤
        (Θ + |Real.log C1| + |Real.log (Real.log 2)| + |Real.log R|) * Real.log K := by
    have hlogC1 : Real.log C1 ≤ |Real.log C1| * Real.log K := by
      calc
        Real.log C1 ≤ |Real.log C1| := le_abs_self _
        _ ≤ |Real.log C1| * Real.log K := by
          nlinarith [abs_nonneg (Real.log C1)]
    have hlogR : Real.log R ≤ |Real.log R| * Real.log K := by
      calc
        Real.log R ≤ |Real.log R| := le_abs_self _
        _ ≤ |Real.log R| * Real.log K := by
          nlinarith [abs_nonneg (Real.log R)]
    have hloglog2 : -Real.log (Real.log 2) ≤
        |Real.log (Real.log 2)| * Real.log K := by
      calc
        -Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := neg_le_abs _
        _ ≤ |Real.log (Real.log 2)| * Real.log K := by
          nlinarith [abs_nonneg (Real.log (Real.log 2))]
    have hbonus : 0 ≤ |Real.log (Real.log 2)| * Real.log K := by positivity
    nlinarith [hll, hloglogD]
  unfold sourceSigma
  calc
    (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) ≤
        (C1 ^ (1 / d) * K ^ (Θ / d)) *
          ((Θ + |Real.log C1| + |Real.log (Real.log 2)| + |Real.log R|) * Real.log K) := by
      gcongr
      exact (Real.log_pos hlog27D_one).le
    _ = _ := by
      dsimp [R]
      ring

theorem claim145_caseA_highS_log_gain_of_growth_with_constant
    {D K s d C1 Θ A : ℝ}
    (hD : 1 < D) (hK : 1 < K) (hs : 1 < s)
    (hC1 : 0 < C1)
    (hchain : Real.log D ≤ C1 * (16 : ℝ) ^ Θ * s ^ (2 * Θ) *
      (Real.log s) ^ (2 * Θ))
    (hgrowth :
      (Real.exp A * C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
          (Real.log (3 * K) * (Real.log (3 * s)) ^ 2) ≤
        s ^ (d - 2 * Θ)) :
    s * (Real.log (Real.log (3 * K)) +
        2 * Real.log (Real.log (3 * s)) + A) ≤
      s * Real.log (1 + s ^ d / Real.log D) := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogK3 : 0 < Real.log (3 * K) := Real.log_pos (by nlinarith)
  have hlogs3 : 0 < Real.log (3 * s) := Real.log_pos (by nlinarith)
  have hs0 : 0 < s := by linarith
  have hlogs : 0 < Real.log s := Real.log_pos hs
  let B : ℝ := Real.exp A * (Real.log (3 * K) * (Real.log (3 * s)) ^ 2)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hdenBound : Real.log D * B ≤ s ^ d := by
    have hchain' := mul_le_mul_of_nonneg_right hchain hB.le
    have hpowid : s ^ d = s ^ (d - 2 * Θ) * s ^ (2 * Θ) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    rw [hpowid]
    dsimp [B] at hchain' ⊢
    have hsPow : 0 ≤ s ^ (2 * Θ) := Real.rpow_nonneg hs0.le _
    calc
      Real.log D *
          (Real.exp A * (Real.log (3 * K) * Real.log (3 * s) ^ 2)) ≤
          (C1 * 16 ^ Θ * s ^ (2 * Θ) * Real.log s ^ (2 * Θ)) *
            (Real.exp A * (Real.log (3 * K) * Real.log (3 * s) ^ 2)) := hchain'
      _ = ((Real.exp A * C1 * 16 ^ Θ) * Real.log s ^ (2 * Θ) *
            (Real.log (3 * K) * Real.log (3 * s) ^ 2)) * s ^ (2 * Θ) := by ring
      _ ≤ s ^ (d - 2 * Θ) * s ^ (2 * Θ) :=
        mul_le_mul_of_nonneg_right hgrowth hsPow
  have hratio : B ≤ s ^ d / Real.log D := by
    exact (le_div_iff₀ hlogD).2 (by simpa [mul_comm] using hdenBound)
  have hBone : B ≤ 1 + s ^ d / Real.log D :=
    hratio.trans (le_add_of_nonneg_left (by norm_num))
  have hbase : 0 < 1 + s ^ d / Real.log D := by positivity
  have hlog := Real.log_le_log hB hBone
  have hlogB : Real.log B = A + Real.log (Real.log (3 * K)) +
      2 * Real.log (Real.log (3 * s)) := by
    dsimp [B]
    rw [Real.log_mul (Real.exp_ne_zero A)
      (ne_of_gt (mul_pos hlogK3 (sq_pos_of_pos hlogs3))),
      Real.log_exp, Real.log_mul (ne_of_gt hlogK3)
        (ne_of_gt (sq_pos_of_pos hlogs3)), Real.log_pow]
    ring
  rw [hlogB] at hlog
  apply mul_le_mul_of_nonneg_left _ hs0.le
  linarith

theorem claim145_caseA_highS_log_gain_with_constant_eventually
    {d C1 Θ A : ℝ}
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ) (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ D s : ℝ, 2 ≤ D → 4 ≤ s →
      Real.sqrt K / Real.log K ≤ s →
      Real.log K ≤ 4 * Real.log s →
      Real.log D ≤ C1 * K ^ Θ →
      s * (Real.log (Real.log (3 * K)) +
          2 * Real.log (Real.log (3 * s)) + A) ≤
        s * Real.log (1 + s ^ d / Real.log D) := by
  let B : ℝ := 32 * Real.exp A * C1 * (16 : ℝ) ^ Θ
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have htail := (isLittleO_log_rpow_rpow_atTop (2 * Θ + 3) hgap).bound
    (show (0 : ℝ) < 1 / (B + 1) by positivity)
  have hsqrtLarge := (isLittleO_log_rpow_rpow_atTop 3 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hS : ∀ᶠ t : ℝ in atTop,
      B * (Real.log t) ^ (2 * Θ + 3) ≤ t ^ (d - 2 * Θ) := by
    filter_upwards [htail, Filter.eventually_ge_atTop 2] with t htail' ht2
    have ht0 : 0 < t := by linarith
    have hpow : 0 ≤ t ^ (d - 2 * Θ) := Real.rpow_nonneg ht0.le _
    change |(Real.log t) ^ (2 * Θ + 3)| ≤
      1 / (B + 1) * |t ^ (d - 2 * Θ)| at htail'
    rw [abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _),
      abs_of_nonneg hpow] at htail'
    have hscaled := mul_le_mul_of_nonneg_left htail' hBpos.le
    have hfrac : B * (1 / (B + 1)) ≤ 1 := by
      rw [div_eq_mul_inv, ← mul_assoc]
      exact (div_le_one (by positivity : 0 < B + 1)).2 (by linarith)
    calc
      B * (Real.log t) ^ (2 * Θ + 3) ≤
          (B * (1 / (B + 1))) * t ^ (d - 2 * Θ) := by nlinarith
      _ ≤ 1 * t ^ (d - 2 * Θ) := mul_le_mul_of_nonneg_right hfrac hpow
      _ = _ := one_mul _
  rcases eventually_atTop.1 hS with ⟨S0, hS0⟩
  have hsqrtS : ∀ᶠ K : ℝ in atTop, S0 ≤ Real.sqrt K / Real.log K := by
    have hM0 : 0 ≤ max S0 4 := le_trans (by norm_num) (le_max_right S0 4)
    have hlarge :=
      (isLittleO_log_rpow_rpow_atTop 1 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
        (show (0 : ℝ) < 1 / (max S0 4 + 1) by positivity)
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hlarge]
        with K hKone hlogK1' hlarge'
    have hK0 : 0 < K := by linarith
    have hlogK : 0 < Real.log K := zero_lt_one.trans_le hlogK1'
    change |Real.log K ^ (1 : ℝ)| ≤
      1 / (max S0 4 + 1) * |K ^ (1 / 2 : ℝ)| at hlarge'
    rw [Real.rpow_one, abs_of_nonneg hlogK.le,
      abs_of_nonneg (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow] at hlarge'
    have hscaled := mul_le_mul_of_nonneg_left hlarge' hM0
    have hfrac : max S0 4 / (max S0 4 + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < max S0 4 + 1)).2 (by linarith)
    have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    have hmain : max S0 4 * Real.log K ≤ Real.sqrt K := by
      calc
        _ ≤ max S0 4 * (1 / (max S0 4 + 1) * Real.sqrt K) := hscaled
        _ = (max S0 4 / (max S0 4 + 1)) * Real.sqrt K := by field_simp
        _ ≤ 1 * Real.sqrt K := mul_le_mul_of_nonneg_right hfrac hsqrt0
        _ = _ := one_mul _
    apply (le_div_iff₀ hlogK).2
    exact (mul_le_mul_of_nonneg_right (le_max_left S0 4) hlogK.le).trans hmain
  filter_upwards [eventually_ge_atTop (3 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      claim145_caseA_highS_log_relation_eventually, hsqrtS]
      with K hK3 hlogK1 hrel hsqrtSK
  have hK1 : 1 < K := lt_of_lt_of_le (by norm_num) hK3
  refine ⟨(show (2 : ℝ) ≤ K by linarith), ?_⟩
  intro D s hD hs hsqrt hlogrel hsmall
  have hD1 : 1 < D := by linarith
  have hs1 : 1 < s := by linarith
  have hlog3s : Real.log (3 * s) ≤ 2 * Real.log s := by
    have hs0 : 0 < s := by linarith
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hs0)]
    have hlog3le : Real.log 3 ≤ Real.log s :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hs0 (by linarith : (3 : ℝ) ≤ s)
    linarith
  have hlog3s0 : 0 ≤ Real.log (3 * s) := (Real.log_pos (by nlinarith)).le
  have hlog3K : Real.log (3 * K) ≤ 2 * Real.log K := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (ne_of_gt (by linarith : 0 < K))]
    have hlog3le : Real.log 3 ≤ Real.log K :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) (by linarith : 0 < K)
        (by linarith : (3 : ℝ) ≤ K)
    linarith
  have hBbound :
      Real.log (3 * K) * (Real.log (3 * s)) ^ 2 ≤ 32 * (Real.log s) ^ 3 := by
    have hsq : (Real.log (3 * s)) ^ 2 ≤ 4 * (Real.log s) ^ 2 := by
      have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
      have hh := (sq_le_sq₀ hlog3s0 (by positivity : 0 ≤ 2 * Real.log s)).2 hlog3s
      nlinarith
    calc
      Real.log (3 * K) * (Real.log (3 * s)) ^ 2 ≤
          (2 * Real.log K) * (4 * (Real.log s) ^ 2) := by
        gcongr
      _ ≤ (8 * Real.log s) * (4 * (Real.log s) ^ 2) := by
        have hsq0 : 0 ≤ 4 * (Real.log s) ^ 2 := by positivity
        nlinarith
      _ = 32 * (Real.log s) ^ 3 := by ring
  have hchain := claim145_caseA_highS_power_chain hK1 hsqrt hlogrel hC1.le hΘ hsmall
  have hgrowth :
      (Real.exp A * C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
          (Real.log (3 * K) * (Real.log (3 * s)) ^ 2) ≤
        s ^ (d - 2 * Θ) := by
    have hfront : 0 ≤ Real.exp A * C1 * (16 : ℝ) ^ Θ * (Real.log s) ^ (2 * Θ) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos A).le hC1.le)
        (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
    have hsGrow :
        B * (Real.log s) ^ (2 * Θ + 3) ≤ s ^ (d - 2 * Θ) :=
      hS0 s (hsqrtSK.trans hsqrt)
    have hpowSplit :
        (Real.log s) ^ (2 * Θ) * (32 * (Real.log s) ^ 3) =
          32 * (Real.log s) ^ (2 * Θ + 3) := by
      calc
        _ = 32 * ((Real.log s) ^ (2 * Θ) * (Real.log s) ^ 3) := by ring
        _ = _ := by
          rw [← Real.rpow_natCast (Real.log s) 3,
            ← Real.rpow_add (Real.log_pos (by linarith : 1 < s))]
          norm_num
    calc
      (Real.exp A * C1 * 16 ^ Θ) * Real.log s ^ (2 * Θ) *
          (Real.log (3 * K) * Real.log (3 * s) ^ 2) ≤
        (Real.exp A * C1 * 16 ^ Θ) * Real.log s ^ (2 * Θ) *
          (32 * (Real.log s) ^ 3) := by
            exact mul_le_mul_of_nonneg_left hBbound hfront
      _ = B * (Real.log s) ^ (2 * Θ + 3) := by
        dsimp [B]
        calc
          _ = (Real.exp A * C1 * 16 ^ Θ) *
              (Real.log s ^ (2 * Θ) * (32 * Real.log s ^ 3)) := by ring
          _ = _ := by rw [hpowSplit]; ring
      _ ≤ s ^ (d - 2 * Θ) := hsGrow
  exact claim145_caseA_highS_log_gain_of_growth_with_constant
    hD1 hK1 hs1 hC1 hchain hgrowth

theorem claim145_caseA_highS_exp_le_profile
    {D K s d C : ℝ}
    (hD : 1 < D) (hK : 1 < K) (hs : 4 ≤ s)
    (hL1 : 1 ≤ suzukiSourceL D K)
    (hsourceLarge : Real.exp 1 * suzukiSourceL D K ≤ s - 2)
    (hLprod : suzukiSourceL D K ≤ Real.log (3 * K) * Real.log (3 * s))
    (hgain :
      s * (Real.log (Real.log (3 * K)) +
          2 * Real.log (Real.log (3 * s)) + (C + 3 + Real.log 2)) ≤
        s * Real.log (1 + s ^ d / Real.log D)) :
    Real.exp
        (suzukiSourceL D K +
          (s - 2) *
            (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2))) ≤
      (1 + s ^ d / Real.log D) ^ s * proposition131iiLowerProfile C s := by
  have hs0 : 0 < s := by linarith
  have hs2 : 0 < s - 2 := by linarith
  have hLs : suzukiSourceL D K ≤ s := by
    have hE : 1 ≤ Real.exp 1 := (Real.one_le_exp zero_le_one)
    have hL0 : 0 ≤ suzukiSourceL D K := by linarith
    have hmul : suzukiSourceL D K ≤ Real.exp 1 * suzukiSourceL D K := by
      nlinarith [mul_le_mul_of_nonneg_right hE hL0]
    linarith
  have hlogHalf : Real.log s - Real.log 2 ≤ Real.log (s - 2) := by
    have hsHalf : s / 2 ≤ s - 2 := by linarith
    rw [← Real.log_div (ne_of_gt hs0) (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) hsHalf
  have hlogL0 : 0 ≤ Real.log (suzukiSourceL D K) := Real.log_nonneg hL1
  have hlog3K : 0 < Real.log (3 * K) := Real.log_pos (by nlinarith)
  have hlog3s : 0 < Real.log (3 * s) := Real.log_pos (by nlinarith)
  have hlogL :
      Real.log (suzukiSourceL D K) ≤
        Real.log (Real.log (3 * K)) + Real.log (Real.log (3 * s)) := by
    have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hL1) hLprod
    rw [Real.log_mul (ne_of_gt hlog3K) (ne_of_gt hlog3s)] at h
    exact h
  have htwoLogs : 2 * Real.log s ≤ s := by
    have hsdiv : 0 < s / 2 := by positivity
    have hlogdiv := Real.log_le_sub_one_of_pos hsdiv
    have hlog2 : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    have hlogeq : Real.log s = Real.log 2 + Real.log (s / 2) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : s / 2 ≠ 0)]
      congr 1
      ring
    rw [hlogeq]
    nlinarith
  have hExp :
      suzukiSourceL D K +
          (s - 2) * (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2)) ≤
        s * (Real.log (Real.log (3 * K)) +
          Real.log (Real.log (3 * s)) + (3 + Real.log 2)) -
          s * Real.log s := by
    have hstep :
        suzukiSourceL D K +
            (s - 2) * (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2)) ≤
          suzukiSourceL D K + s + s * Real.log (suzukiSourceL D K) -
            (s - 2) * (Real.log s - Real.log 2) := by
      have h1 : (s - 2) * Real.log (suzukiSourceL D K) ≤ s * Real.log (suzukiSourceL D K) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hlogL0
      have h2 : -(s - 2) * Real.log (s - 2) ≤ -(s - 2) * (Real.log s - Real.log 2) := by
        nlinarith
      nlinarith
    have hstep' :
        suzukiSourceL D K + s + s * Real.log (suzukiSourceL D K) -
            (s - 2) * (Real.log s - Real.log 2) ≤
          s * Real.log (suzukiSourceL D K) + (3 + Real.log 2) * s -
            s * Real.log s := by
      have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      nlinarith [hLs, htwoLogs]
    have hstep'' :
        s * Real.log (suzukiSourceL D K) + (3 + Real.log 2) * s - s * Real.log s ≤
          s * (Real.log (Real.log (3 * K)) +
            Real.log (Real.log (3 * s)) + (3 + Real.log 2)) -
            s * Real.log s := by
      have hm := mul_le_mul_of_nonneg_left hlogL hs0.le
      nlinarith
    exact hstep.trans <| hstep'.trans hstep''
  have hfinalExp :
      suzukiSourceL D K +
          (s - 2) * (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2)) ≤
        s * Real.log (1 + s ^ d / Real.log D) -
          s * Real.log s - s * Real.log (Real.log (3 * s)) - C * s := by
    have := hgain
    nlinarith [hExp]
  apply Real.exp_le_exp.mpr at hfinalExp
  unfold proposition131iiLowerProfile
  calc
    _ ≤ Real.exp (s * Real.log (1 + s ^ d / Real.log D) -
        s * Real.log s - s * Real.log (Real.log (3 * s)) - C * s) := hfinalExp
    _ = _ := by
      have hlogD : 0 < Real.log D := Real.log_pos hD
      have hbase : 0 < 1 + s ^ d / Real.log D := by
        have hpow : 0 ≤ s ^ d := Real.rpow_nonneg hs0.le _
        positivity
      rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
      congr 1
      ring

theorem claim145_caseA_highS_front_factor_eventually_uniform_in_S
    {d Δ C1 Θ : ℝ}
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ (S : BoundingSieve) (D s : ℝ),
      HasDimensionOneLocalProductBound S K →
      2 ≤ D → 4 ≤ s →
      Real.sqrt K / Real.log K ≤ s →
      Real.log D ≤ C1 * K ^ Θ →
      1 ≤ claim14_5VProduct S D *
        (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) *
        s * (Real.log D) ^ (-Δ) := by
  have hd0 : 0 < d := by linarith
  let Aσ : ℝ :=
    (C1 ^ (1 / d)) *
      (Θ + |Real.log C1| + |Real.log (Real.log 2)| +
        |Real.log (Real.log 27 / Real.log 2 + 1)|)
  have hAσ : 0 ≤ Aσ := by dsimp [Aσ]; positivity
  have hpowGap : 0 < (d - 2 * Θ) / (2 * d) := by positivity
  have hdom0 := (isLittleO_log_rpow_rpow_atTop 2 hpowGap).bound
    (show (0 : ℝ) < 1 / (Aσ + 1) by positivity)
  have hdom : ∀ᶠ K : ℝ in atTop,
      Aσ * (Real.log K) ^ 2 ≤ K ^ ((d - 2 * Θ) / (2 * d)) := by
    filter_upwards [hdom0, eventually_ge_atTop (1 : ℝ)] with K hK hK1
    have hpow0 : 0 ≤ K ^ ((d - 2 * Θ) / (2 * d)) :=
      Real.rpow_nonneg (by linarith) _
    change |(Real.log K) ^ (2 : ℝ)| ≤
      1 / (Aσ + 1) * |K ^ ((d - 2 * Θ) / (2 * d))| at hK
    rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hpow0] at hK
    have hscaled := mul_le_mul_of_nonneg_left hK hAσ
    have hfrac : Aσ * (1 / (Aσ + 1)) ≤ 1 := by
      rw [div_eq_mul_inv, ← mul_assoc]
      exact (div_le_one (by positivity : 0 < Aσ + 1)).2 (by linarith)
    calc
      Aσ * (Real.log K) ^ 2 ≤
          (Aσ * (1 / (Aσ + 1))) * K ^ ((d - 2 * Θ) / (2 * d)) := by
            nlinarith
      _ ≤ 1 * K ^ ((d - 2 * Θ) / (2 * d)) :=
        mul_le_mul_of_nonneg_right hfrac hpow0
      _ = _ := one_mul _
  let Q : ℝ := 3 * |Real.log C1| + |Real.log (Real.log 2)| + 3 * Θ + 2
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hprefLog0 := (isLittleO_log_rpow_rpow_atTop 1
      (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / (4 * (Q + 1)) by positivity)
  have hpref0 : ∀ᶠ K : ℝ in atTop, ∀ D : ℝ, 2 ≤ D →
      Real.log D ≤ C1 * K ^ Θ →
      (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) ≤ Real.exp (Real.sqrt K / 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.tendsto_sqrt_atTop.eventually_ge_atTop (4 * Q), hprefLog0]
      with K hK3 hlogK1 hsqrtQ hsmallLog
    have hK0 : 0 < K := by linarith
    have hK1 : 1 < K := by linarith
    have hlogK : 0 < Real.log K := zero_lt_one.trans_le hlogK1
    have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    change |Real.log K ^ (1 : ℝ)| ≤
      1 / (4 * (Q + 1)) * |K ^ (1 / 2 : ℝ)| at hsmallLog
    rw [Real.rpow_one, abs_of_nonneg hlogK.le,
      abs_of_nonneg (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow] at hsmallLog
    have hscaled := mul_le_mul_of_nonneg_left hsmallLog hQ0
    have hfrac : Q / (Q + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < Q + 1)).2 (by linarith)
    have hQlog : Q * Real.log K ≤ Real.sqrt K / 4 := by
      calc
        _ ≤ Q * (1 / (4 * (Q + 1)) * Real.sqrt K) := hscaled
        _ = (Q / (Q + 1)) * (Real.sqrt K / 4) := by field_simp
        _ ≤ 1 * (Real.sqrt K / 4) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
        _ = _ := one_mul _
    have hQ : Q ≤ Real.sqrt K / 4 := by nlinarith
    intro D hD hsmall
    have hD1 : 1 < D := by linarith
    have hlogD : 0 < Real.log D := Real.log_pos hD1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hKpow : 0 < K ^ Θ := Real.rpow_pos_of_pos hK0 _
    have hloglogD : Real.log (Real.log D) ≤ Real.log C1 + Θ * Real.log K := by
      have hh := Real.log_le_log hlogD hsmall
      rw [Real.log_mul (ne_of_gt hC1) (ne_of_gt hKpow), Real.log_rpow hK0 Θ] at hh
      exact hh
    have hbaseK : 1 + K / Real.log 2 ≤ K ^ 2 := by
      have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
        linarith [Real.log_two_gt_d9]
      have hpart : K / Real.log 2 ≤ 2 * K := by
        apply (div_le_iff₀ hlog2).2
        nlinarith
      nlinarith [sq_nonneg (K - 3)]
    have hlogbase : Real.log (1 + K / Real.log 2) ≤ 2 * Real.log K := by
      have hbpos : 0 < 1 + K / Real.log 2 := by positivity
      have hh := Real.log_le_log hbpos hbaseK
      rw [Real.log_pow] at hh
      simpa using hh
    have hc0 : 0 ≤ 2 + Δ := by linarith
    have hc3 : 2 + Δ ≤ 3 := by linarith
    have hmain := mul_le_mul_of_nonneg_left hloglogD hc0
    have hCterm : (2 + Δ) * Real.log C1 ≤ 3 * |Real.log C1| := by
      calc
        _ ≤ (2 + Δ) * |Real.log C1| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hc0
        _ ≤ _ := mul_le_mul_of_nonneg_right hc3 (abs_nonneg _)
    have hΘterm : (2 + Δ) * (Θ * Real.log K) ≤ 3 * Θ * Real.log K := by
      nlinarith [mul_le_mul_of_nonneg_right hc3
        (mul_nonneg hΘ hlogK.le)]
    let P := (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
      (Real.log D) ^ (1 + Δ)
    have hPpos : 0 < P := by dsimp [P]; positivity
    have hlogP : Real.log P ≤ Q * (Real.log K + 1) := by
      dsimp [P]
      rw [Real.log_mul (by positivity : Real.log D / Real.log 2 *
          (1 + K / Real.log 2) ≠ 0) (by positivity : Real.log D ^ (1 + Δ) ≠ 0),
        Real.log_mul (by positivity : Real.log D / Real.log 2 ≠ 0)
          (by positivity : 1 + K / Real.log 2 ≠ 0),
        Real.log_div hlogD.ne' hlog2.ne', Real.log_rpow hlogD]
      have hid : Real.log (Real.log D) - Real.log (Real.log 2) +
          Real.log (1 + K / Real.log 2) + (1 + Δ) * Real.log (Real.log D) =
          (2 + Δ) * Real.log (Real.log D) + Real.log (1 + K / Real.log 2) -
            Real.log (Real.log 2) := by ring
      rw [hid]
      have hmain' : (2 + Δ) * Real.log (Real.log D) ≤
          3 * |Real.log C1| + 3 * Θ * Real.log K := by
        calc
          _ ≤ (2 + Δ) * Real.log C1 + (2 + Δ) * (Θ * Real.log K) := by
            nlinarith [hmain]
          _ ≤ _ := by nlinarith [hCterm, hΘterm]
      have hCscale : 3 * |Real.log C1| ≤
          3 * |Real.log C1| * Real.log K := by
        nlinarith [mul_le_mul_of_nonneg_left hlogK1
          (show 0 ≤ 3 * |Real.log C1| by positivity)]
      have hAscale : |Real.log (Real.log 2)| ≤
          |Real.log (Real.log 2)| * Real.log K := by
        nlinarith [mul_le_mul_of_nonneg_left hlogK1
          (abs_nonneg (Real.log (Real.log 2)))]
      have hsimple : (2 + Δ) * Real.log (Real.log D) +
          Real.log (1 + K / Real.log 2) - Real.log (Real.log 2) ≤
          Q * Real.log K := by
        dsimp [Q]
        nlinarith [hmain', hlogbase, hCscale, hAscale,
          neg_le_abs (Real.log (Real.log 2))]
      exact hsimple.trans (by nlinarith [mul_nonneg hQ0 hlogK.le])
    calc
      P = Real.exp (Real.log P) := (Real.exp_log hPpos).symm
      _ ≤ Real.exp (Real.sqrt K / 2) := by
        apply Real.exp_le_exp.mpr
        exact hlogP.trans (by nlinarith [hQlog, hQ])
  filter_upwards [eventually_ge_atTop (3 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hdom, hpref0]
      with K hK3 hlogK1 hdomK hpref0K
  have hK1 : 1 < K := lt_of_lt_of_le (by norm_num) hK3
  have hlogK : 0 < Real.log K := zero_lt_one.trans_le hlogK1
  refine ⟨(show (2 : ℝ) ≤ K by linarith), ?_⟩
  intro S D s hlocal hD hs hsqrt hsmall
  have hσbound :=
    claim145_caseA_highS_sourceSigma_le_Kbound (D := D) (K := K) (C1 := C1)
      (Θ := Θ) (d := d) hD hK3 hlogK1 hC1 hΘ hd0 hsmall
  have hsigmaMain : sourceSigma D d ≤ Real.sqrt K / Real.log K := by
    calc
      sourceSigma D d ≤ Aσ * K ^ (Θ / d) * Real.log K := by
        simpa [Aσ] using hσbound
      _ ≤ K ^ ((d - 2 * Θ) / (2 * d)) *
          (K ^ (Θ / d) / Real.log K) := by
        have hscale : 0 ≤ K ^ (Θ / d) / Real.log K := by positivity
        have hh := mul_le_mul_of_nonneg_right hdomK hscale
        rw [show Aσ * K ^ (Θ / d) * Real.log K =
          (Aσ * Real.log K ^ 2) * (K ^ (Θ / d) / Real.log K) by
            field_simp [hlogK.ne']]
        exact hh
      _ = Real.sqrt K / Real.log K := by
        have hsum : (d - 2 * Θ) / (2 * d) + Θ / d = (1 / 2 : ℝ) := by
          field_simp [hd0.ne']
          ring
        rw [show K ^ ((d - 2 * Θ) / (2 * d)) *
            (K ^ (Θ / d) / Real.log K) =
            (K ^ ((d - 2 * Θ) / (2 * d)) * K ^ (Θ / d)) / Real.log K by ring,
          ← Real.rpow_add (by linarith : 0 < K), hsum, Real.sqrt_eq_rpow]
  have hsigmaLe : sourceSigma D d ≤ s := hsigmaMain.trans hsqrt
  have hprefBase :
      (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) ≤ Real.exp (Real.sqrt K / 2) :=
    hpref0K D hD hsmall
  have hlocalFactor :=
    claim14_5VProduct_lower_of_localProduct (S := S) (D := D) (K := K) hD hlocal
  have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
  have hσpos : 0 < sourceSigma D d := by
    unfold sourceSigma
    have hinner : 1 < Real.log (27 * D) := by
      rw [Real.lt_log_iff_exp_lt (by positivity : 0 < 27 * D)]
      nlinarith [Real.exp_one_lt_three]
    exact mul_pos (Real.rpow_pos_of_pos hlogD _) (Real.log_pos hinner)
  have haux :
      (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) * sourceSigma D d ≤
        s * Real.exp (Real.sqrt K) := by
    calc
      _ ≤ Real.exp (Real.sqrt K / 2) * s := by gcongr
      _ ≤ s * Real.exp (Real.sqrt K) := by
        have he : Real.exp (Real.sqrt K / 2) ≤ Real.exp (Real.sqrt K) := by
          exact Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg K])
        nlinarith [mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ s)]
  let R := (Real.log D / Real.log 2) * (1 + K / Real.log 2)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hdenpos : 0 < R * (Real.log D) ^ (1 + Δ) * sourceSigma D d := by
    positivity
  have hdiv : 1 ≤ (s * Real.exp (Real.sqrt K)) /
      (R * (Real.log D) ^ (1 + Δ) * sourceSigma D d) :=
    (le_div_iff₀ hdenpos).2 (by simpa [R] using haux)
  have hscaleR : R ≤
      (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) * s *
        (Real.log D) ^ (-Δ) := by
    have hh := mul_le_mul_of_nonneg_left hdiv hRpos.le
    calc
      R = R * 1 := (mul_one R).symm
      _ ≤ R * ((s * Real.exp (Real.sqrt K)) /
          (R * (Real.log D) ^ (1 + Δ) * sourceSigma D d)) := hh
      _ = _ := by
        dsimp [R]
        rw [Real.rpow_neg hlogD.le, Real.rpow_add hlogD, Real.rpow_one]
        field_simp [hlogD.ne', hσpos.ne',
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hscale0 : 0 ≤
      (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) * s *
        (Real.log D) ^ (-Δ) := by positivity
  have hV : 0 ≤ claim14_5VProduct S D := by
    dsimp [claim14_5VProduct]
    apply Finset.prod_nonneg
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpS)
      (Nat.mem_primeFactors.mp hpS).2.1).le
  calc
    1 ≤ claim14_5VProduct S D *
        ((Real.log D / Real.log 2) * (1 + K / Real.log 2)) := hlocalFactor
    _ ≤ claim14_5VProduct S D *
        ((Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) * s *
          (Real.log D) ^ (-Δ)) := by
      dsimp [R] at hscaleR
      exact mul_le_mul_of_nonneg_left hscaleR hV
    _ = _ := by ring

/-- Compatibility specialization of the uniform front-factor cutoff. -/
theorem claim145_caseA_highS_front_factor_eventually
    (S : BoundingSieve) {d Δ C1 Θ : ℝ}
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ D s : ℝ,
      HasDimensionOneLocalProductBound S K →
      2 ≤ D → 4 ≤ s →
      Real.sqrt K / Real.log K ≤ s →
      Real.log D ≤ C1 * K ^ Θ →
      1 ≤ claim14_5VProduct S D *
        (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) *
        s * (Real.log D) ^ (-Δ) := by
  filter_upwards [claim145_caseA_highS_front_factor_eventually_uniform_in_S
    hC1 hΘ hΔ0 hΔ1 hgap] with K hK
  exact ⟨hK.1, hK.2 S⟩

/-- Final high-coordinate `(14.6)` scalar absorption.  Unlike an actual-bound
wrapper, this statement exposes the complete numerical comparison: the finite
Euler reciprocal (through `claim14_5VProduct`), the moving `sourceSigma`, all
logarithmic powers, and the uniform linear loss `C*s` from Proposition 13.1(ii).
The hypotheses `hL1`, `hsourceLarge`, and `hLprod` are precisely the already
proved Lemma-14.3 high-coordinate transition conditions; the only eventual
work left here is the source-small-`D` absorption, uniformly in `D` and `s`. -/
theorem claim145_caseA_highS_habsorb_eventually_uniform_in_S
    {d Δ C1 Θ C : ℝ}
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ (S : BoundingSieve) (D s : ℝ),
      HasDimensionOneLocalProductBound S K →
      2 ≤ D → 4 ≤ s →
      Real.sqrt K / Real.log K ≤ s →
      Real.log D ≤ C1 * K ^ Θ →
      1 ≤ suzukiSourceL D K →
      Real.exp 1 * suzukiSourceL D K ≤ s - 2 →
      suzukiSourceL D K ≤ Real.log (3 * K) * Real.log (3 * s) →
      Real.exp
          (suzukiSourceL D K + (s - 2) *
            (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2))) ≤
        claim14_5VProduct S D *
          (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) *
          ((1 + s ^ d / Real.log D) ^ s * s *
            proposition131iiLowerProfile C s) *
          (Real.log D) ^ (-Δ) := by
  filter_upwards [claim145_caseA_highS_log_gain_with_constant_eventually
      (d := d) (C1 := C1) (Θ := Θ) (A := C + 3 + Real.log 2)
      hC1 hΘ hgap,
    claim145_caseA_highS_front_factor_eventually_uniform_in_S hC1 hΘ hΔ0 hΔ1 hgap,
    claim145_caseA_highS_log_relation_eventually]
      with K hgainK hfrontK hrelK
  refine ⟨hgainK.1, ?_⟩
  intro S D s hlocal hD hs hsqrt hsmall hL1 hsourceLarge hLprod
  have hlogrel : Real.log K ≤ 4 * Real.log s := hrelK.2 s hsqrt
  have hgain' := hgainK.2 D s hD hs hsqrt hlogrel hsmall
  have hexp := claim145_caseA_highS_exp_le_profile
    (D := D) (K := K) (s := s) (d := d) (C := C)
    (by linarith) (by linarith) hs hL1 hsourceLarge hLprod hgain'
  have hfront := hfrontK.2 S D s hlocal hD hs hsqrt hsmall
  have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
  have hbase : 0 < 1 + s ^ d / Real.log D := by positivity
  have htail0 : 0 ≤ (1 + s ^ d / Real.log D) ^ s *
      proposition131iiLowerProfile C s := by
    exact mul_nonneg (Real.rpow_nonneg hbase.le _) (Real.exp_pos _).le
  calc
    _ ≤ (1 + s ^ d / Real.log D) ^ s *
        proposition131iiLowerProfile C s := hexp
    _ ≤ (claim14_5VProduct S D *
          (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) *
          s * (Real.log D) ^ (-Δ)) *
        ((1 + s ^ d / Real.log D) ^ s *
          proposition131iiLowerProfile C s) := by
      calc
        _ = 1 * ((1 + s ^ d / Real.log D) ^ s *
            proposition131iiLowerProfile C s) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfront htail0
    _ = _ := by ring

/-- Compatibility specialization of the uniform high-coordinate absorption. -/
theorem claim145_caseA_highS_habsorb_eventually
    (S : BoundingSieve) {d Δ C1 Θ C : ℝ}
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ D s : ℝ,
      HasDimensionOneLocalProductBound S K →
      2 ≤ D → 4 ≤ s →
      Real.sqrt K / Real.log K ≤ s →
      Real.log D ≤ C1 * K ^ Θ →
      1 ≤ suzukiSourceL D K →
      Real.exp 1 * suzukiSourceL D K ≤ s - 2 →
      suzukiSourceL D K ≤ Real.log (3 * K) * Real.log (3 * s) →
      Real.exp
          (suzukiSourceL D K + (s - 2) *
            (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2))) ≤
        claim14_5VProduct S D *
          (Real.exp (Real.sqrt K) / (Real.log D * sourceSigma D d)) *
          ((1 + s ^ d / Real.log D) ^ s * s *
            proposition131iiLowerProfile C s) *
          (Real.log D) ^ (-Δ) := by
  filter_upwards [claim145_caseA_highS_habsorb_eventually_uniform_in_S
    hC1 hΘ hΔ0 hΔ1 hgap] with K hK
  exact ⟨hK.1, hK.2 S⟩


end MathlibNt.SieveTheory
