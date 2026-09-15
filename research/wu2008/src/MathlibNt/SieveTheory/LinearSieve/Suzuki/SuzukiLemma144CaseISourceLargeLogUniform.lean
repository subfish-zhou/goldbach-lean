import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseI1423SigmaCubedDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceParameters

open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Case I: source-faithful uniform scalar cutoff

This proves the literal `(14.23)` scalar estimate uniformly in `K` directly
from Suzuki's parameter packet.  It uses the exact source margin
`2 / Θ + 3 / d < 1 - Δ`; in particular it does not replace `Δ` by
`Δ + 2 / Θ` in the older sufficient condition `7 / (1 - Δ) < d`.
-/

/-- Under the source parameter packet, the literal Case-I `(14.23)` scalar has
one cutoff in the separator `C1`, chosen before arbitrary `K` and `D`. -/
theorem exists_caseI1423_sourceScalar_sourceLargeLog_uniform_of_source
    {d Δ Θ : ℝ} (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 K D : ℝ), C1min ≤ C1 → 2 ≤ K → 2 ≤ D →
        C1 * K ^ Θ < Real.log D →
        K ^ 2 * sourceSigma D d ^ 3 *
            Real.log (Real.exp 1 * sourceSigma D d) *
            Real.log (Real.log D) /
            (Real.log D) ^ (1 - Δ) ≤ 1 := by
  let η : ℝ := 1 - Δ - (2 / Θ + 3 / d)
  have hη : 0 < η := by
    dsimp [η]
    linarith [hsrc.h14_4]
  let δ : ℝ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hd : 0 < d := hsrc.d_pos
  have hΘ : 0 < Θ := hsrc.hTheta_pos
  have hinvd : 1 / d ≤ 1 := by
    have hd7 : 7 < d := by
      have hβ : 0 < 1 - Δ := sub_pos.mpr hsrc.hDelta_lt
      have hβlt : 1 - Δ < 1 := by linarith [hsrc.hDelta_pos]
      have hquot : 7 < 7 / (1 - Δ) := by
        apply (lt_div_iff₀ hβ).2
        nlinarith
      exact hquot.trans hsrc.h14_1
    have hd1 : 1 < d := by linarith
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd1
    norm_num at h ⊢
    exact h.le
  have hdom0 := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hδ).bound
    (show (0 : ℝ) < 1 / 32 by norm_num)
  obtain ⟨Xlog, hXlog⟩ := eventually_atTop.1 hdom0
  let C1min : ℝ := max (max (Real.exp 1) (max (Real.log 27) 2)) Xlog
  have hC1min : 1 ≤ C1min := by
    exact (Real.one_le_exp (by norm_num)).trans
      ((le_max_left (Real.exp 1) (max (Real.log 27) 2)).trans
        (le_max_left _ _))
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 K D hC1 hK hD2 hlarge
  let x : ℝ := Real.log D
  let q : ℝ := Real.log x
  let ell : ℝ := Real.log (Real.log (27 * D))
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKΘ1 : 1 ≤ K ^ Θ := Real.one_le_rpow hK1 hΘ.le
  have hxC1 : C1 < x := by
    calc
      C1 ≤ C1 * K ^ Θ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKΘ1
          (zero_le_one.trans (hC1min.trans hC1))
      _ < x := by simpa [x] using hlarge
  have hxMin : C1min < x := hC1.trans_lt hxC1
  have hxe : Real.exp 1 < x :=
    ((le_max_left (Real.exp 1) (max (Real.log 27) 2)).trans
      (le_max_left _ _)).trans_lt hxMin
  have hx27 : Real.log 27 ≤ x :=
    ((le_max_left (Real.log 27) 2).trans
      ((le_max_right (Real.exp 1) _).trans (le_max_left _ _))).trans hxMin.le
  have hx2 : 2 ≤ x :=
    ((le_max_right (Real.log 27) 2).trans
      ((le_max_right (Real.exp 1) _).trans (le_max_left _ _))).trans hxMin.le
  have hx : 0 < x := (Real.exp_pos 1).trans hxe
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxe.le
  have hq1 : 1 ≤ q := by
    dsimp [q]
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hx hxe.le
  have hq : 0 < q := zero_lt_one.trans_le hq1
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    dsimp [x]
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hD0)]
  have hinnerPos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    positivity
  have hell : 0 < ell := by
    dsimp [ell]
    apply Real.log_pos
    rw [hlog27D]
    have h27 : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hinnerLower : x ≤ Real.log (27 * D) := by
    rw [hlog27D]
    exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
  have hellLower : q ≤ ell := by
    dsimp [q, ell]
    exact Real.strictMonoOn_log.monotoneOn hx hinnerPos hinnerLower
  have hell1 : 1 ≤ ell := hq1.trans hellLower
  have hinnerUpper : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hellUpper : ell ≤ 2 * q := by
    have h := Real.log_le_log hinnerPos hinnerUpper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    have hlog2le : Real.log 2 ≤ q := by
      dsimp [q]
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    dsimp [ell, q] at h ⊢
    linarith
  have hsigma : 0 < sourceSigma D d := by
    dsimp [sourceSigma, x, ell]
    positivity
  have hsigma1 : 1 ≤ sourceSigma D d := by
    dsimp [sourceSigma, x, ell]
    have hxp : 1 ≤ x ^ (1 / d) := Real.one_le_rpow hx1 (by positivity)
    have hxp0 : 0 ≤ x ^ (1 / d) := Real.rpow_nonneg hx.le _
    nlinarith [mul_le_mul hxp hell1 zero_le_one hxp0]
  have hlogScalar0 : 0 ≤ Real.log (Real.exp 1 * sourceSigma D d) := by
    apply Real.log_nonneg
    have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith [mul_le_mul hexp1 hsigma1 zero_le_one (Real.exp_pos 1).le]
  have hlogScalar : Real.log (Real.exp 1 * sourceSigma D d) ≤ 3 * q := by
    have hlogell : Real.log ell ≤ ell - 1 := Real.log_le_sub_one_of_pos hell
    have hexpand : Real.log (Real.exp 1 * sourceSigma D d) =
        1 + (1 / d) * q + Real.log ell := by
      rw [Real.log_mul (Real.exp_ne_zero 1) hsigma.ne', Real.log_exp]
      dsimp [sourceSigma]
      rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' hell.ne',
        Real.log_rpow hx]
      rw [show Real.log x = q by rfl]
      ring
    rw [hexpand]
    have hterm : (1 / d) * q ≤ q := mul_le_of_le_one_left hq.le hinvd
    linarith
  have hellcube : ell ^ 3 ≤ 8 * q ^ 3 := by
    calc
      ell ^ 3 ≤ (2 * q) ^ 3 := by gcongr
      _ = 8 * q ^ 3 := by ring
  have hpacket : ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q ≤
      32 * q ^ 5 := by
    calc
      ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q ≤
          (8 * q ^ 3) * (3 * q) * q := by gcongr
      _ ≤ 32 * q ^ 5 := by nlinarith [sq_nonneg (q ^ 2)]
  have hKΘ : K ^ Θ < x := by
    calc
      K ^ Θ ≤ C1 * K ^ Θ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hC1min.trans hC1) (Real.rpow_nonneg hK0.le _)
      _ < x := by simpa [x] using hlarge
  have hKsq : K ^ 2 ≤ x ^ (2 / Θ) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le Θ) hKΘ.le
      (show 0 ≤ 2 / Θ by positivity)
    calc
      K ^ 2 = (K ^ Θ) ^ (2 / Θ) := by
        rw [← Real.rpow_mul hK0.le]
        have : Θ * (2 / Θ) = 2 := by field_simp
        rw [this, Real.rpow_two]
      _ ≤ x ^ (2 / Θ) := hp
  have hlogpow : 32 * q ^ 5 ≤ x ^ δ := by
    have hXlogMin : Xlog ≤ C1min := le_max_right _ _
    have h := hXlog x (hXlogMin.trans hxMin.le)
    change |Real.log x ^ (5 : ℝ)| ≤ (1 / 32) * |x ^ δ| at h
    rw [abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      abs_of_nonneg (Real.rpow_nonneg hx.le _)] at h
    norm_num [Real.rpow_natCast] at h
    nlinarith
  have hxpow3 : (x ^ (1 / d)) ^ 3 = x ^ (3 / d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hfront : x ^ (2 / Θ) * x ^ (3 / d) /
      x ^ (1 - Δ) = x ^ (-η) := by
    rw [← Real.rpow_add hx, div_eq_mul_inv, ← Real.rpow_neg hx.le,
      ← Real.rpow_add hx]
    congr 1
    dsimp [η]
    ring
  have halgebra :
      K ^ 2 * sourceSigma D d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma D d) * q /
          x ^ (1 - Δ) =
        (K ^ 2 * x ^ (3 / d) / x ^ (1 - Δ)) *
          (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) := by
    dsimp [sourceSigma, ell]
    rw [mul_pow, hxpow3]
    ring
  rw [show Real.log (Real.log D) = q by rfl,
    show Real.log D = x by rfl, halgebra]
  have hright0 : 0 ≤ ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q := by
    positivity
  have hden0 : 0 < x ^ (1 - Δ) := Real.rpow_pos_of_pos hx _
  calc
    (K ^ 2 * x ^ (3 / d) / x ^ (1 - Δ)) *
        (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) ≤
      (x ^ (2 / Θ) * x ^ (3 / d) / x ^ (1 - Δ)) *
        (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) := by
          gcongr
    _ = x ^ (-η) *
        (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) := by rw [hfront]
    _ ≤ x ^ (-η) * (32 * q ^ 5) := by gcongr
    _ ≤ x ^ (-η) * x ^ δ := by gcongr
    _ = x ^ (-δ) := by
      rw [← Real.rpow_add hx]
      congr 1
      dsimp [δ]
      linarith
    _ ≤ x ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = 1 := by simp


end MathlibNt.SieveTheory
