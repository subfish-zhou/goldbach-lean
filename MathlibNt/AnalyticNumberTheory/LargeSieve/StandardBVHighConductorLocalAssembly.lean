import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorLocalPrimitiveLargeSieve
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVHighHybridFeasibility

/-!
# Scalar Pan-cutoff payment for conductor-local high ledgers

This is the terminal scalar part of the high-source assembly.  All shell,
prefix-maximal, harmonic, and coefficient losses may be collected into a fixed
power `log(N)^κ`.  The conductor exponent pays the `N/√R` lane and Pan's modulus
exponent pays the `Q√N` lane independently.
-/

namespace AnalyticNumberTheory.LargeSieve

open Filter
open scoped Topology

noncomputable section

/-- The choices used by the high-conductor scalar payment. -/
def conductorLocalPanConductorExponent (A κ : ℕ) : ℕ := 2 * (A + κ + 1)

def conductorLocalPanModulusExponent (A κ : ℕ) : ℕ := A + κ

private theorem logPower_le_logConductorThreshold_eventually (A κ : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ (2 * (A + κ)) ≤
        (logConductorThreshold N (conductorLocalPanConductorExponent A κ) : ℝ) := by
  filter_upwards [eventually_ge_atTop (9 : ℕ)] with N hN
  let x : ℝ := Real.log (N : ℝ)
  let t : ℕ := A + κ
  have hx2 : 2 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have he10 : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
    have h9 : Real.exp 2 < (9 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have hexp : Real.exp 2 < (N : ℝ) := h9.trans_le (by exact_mod_cast hN)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2 hexp |>.le
  have hx0 : 0 ≤ x := hx2.trans' (by norm_num)
  have hxpow2 : 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hp2 : 2 ≤ x ^ (2 * (t + 1)) := by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hbase : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hfloor := Nat.sub_one_lt_floor (x ^ (2 * (t + 1)))
  have hhalf : x ^ (2 * t) ≤ x ^ (2 * (t + 1)) - 1 := by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hbase : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hcast : x ^ (2 * t) ≤ (Nat.floor (x ^ (2 * (t + 1))) : ℝ) :=
    hhalf.trans hfloor.le
  simpa [logConductorThreshold, conductorLocalPanConductorExponent, x, t,
    Nat.cast_ofNat] using hcast

/-- Complete scalar payment.  This theorem has no analytic premise: it proves
that the two scales delivered by the conductor-local square ledgers fit the
Standard-BV target after one fixed polylogarithmic shell loss. -/
theorem conductorLocal_high_scales_pan_payable (A κ : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let C := conductorLocalPanConductorExponent A κ
      let B := conductorLocalPanModulusExponent A κ
      let R := logConductorThreshold N C
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      Real.log (N : ℝ) ^ κ *
          ((N : ℝ) / Real.sqrt R + (Q : ℝ) * Real.sqrt N) ≤
        2 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [logPower_le_logConductorThreshold_eventually A κ,
    eventually_ge_atTop (9 : ℕ)] with N hR hN
  let C := conductorLocalPanConductorExponent A κ
  let B := conductorLocalPanModulusExponent A κ
  let R := logConductorThreshold N C
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsN : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hN0
  have hR' : x ^ (2 * (A + κ)) ≤ (R : ℝ) := by
    simpa [R, x] using hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (pow_pos hx _) hR'
  have hsRpos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 hRpos
  have hsR : x ^ (A + κ) ≤ Real.sqrt (R : ℝ) := by
    have hsRsq : Real.sqrt (R : ℝ) ^ 2 = R := Real.sq_sqrt hRpos.le
    have hp : (x ^ (A + κ)) ^ 2 = x ^ (2 * (A + κ)) := by rw [← pow_mul]; congr 1; omega
    have hpow0 : 0 ≤ x ^ (A + κ) := (pow_nonneg hx.le _)
    nlinarith
  have hQ : (Q : ℝ) ≤ Real.sqrt N / x ^ (A + κ) := by
    calc
      (Q : ℝ) =
          (Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) /
            Real.log N ^ ((B : ℕ) : ℝ)) : ℝ) := by
              simp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff]
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) /
          Real.log N ^ ((B : ℕ) : ℝ) := Nat.floor_le (by positivity)
      _ = Real.sqrt N / x ^ (A + κ) := by
        have he : ((B : ℕ) : ℝ) = ((A + κ : ℕ) : ℝ) := by
          simp [B, conductorLocalPanModulusExponent]
        rw [Real.sqrt_eq_rpow, he, Real.rpow_natCast]
  have hfirst : x ^ κ * ((N : ℝ) / Real.sqrt R) ≤ (N : ℝ) / x ^ A := by
    rw [show x ^ κ * ((N : ℝ) / Real.sqrt R) =
      (x ^ κ * (N : ℝ)) / Real.sqrt R by ring]
    apply (div_le_div_iff₀ hsRpos (pow_pos hx A)).2
    calc
      x ^ κ * (N : ℝ) * x ^ A = (N : ℝ) * x ^ (A + κ) := by
        rw [pow_add]
        ring
      _ ≤ (N : ℝ) * Real.sqrt R := by gcongr
  have hsecond : x ^ κ * ((Q : ℝ) * Real.sqrt N) ≤ (N : ℝ) / x ^ A := by
    apply (le_div_iff₀ (pow_pos hx A)).2
    have hden : 0 < x ^ (A + κ) := pow_pos hx _
    have hQ' : (Q : ℝ) * x ^ (A + κ) ≤ Real.sqrt N :=
      (le_div_iff₀ hden).mp hQ
    calc
      x ^ κ * ((Q : ℝ) * Real.sqrt N) * x ^ A =
          Real.sqrt N * ((Q : ℝ) * x ^ (A + κ)) := by
            rw [pow_add]
            ring
      _ ≤ Real.sqrt N * Real.sqrt N := by gcongr
      _ = (N : ℝ) := by rw [← sq, hsN]
  dsimp [C, B, R, Q]
  calc
    x ^ κ * ((N : ℝ) / Real.sqrt (logConductorThreshold N
        (conductorLocalPanConductorExponent A κ)) +
        (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N
          (conductorLocalPanModulusExponent A κ : ℝ) : ℝ) * Real.sqrt N) =
      x ^ κ * ((N : ℝ) / Real.sqrt R) +
        x ^ κ * ((Q : ℝ) * Real.sqrt N) := by ring
    _ ≤ (N : ℝ) / x ^ A + (N : ℝ) / x ^ A := add_le_add hfirst hsecond
    _ = 2 * (N : ℝ) / x ^ A := by ring

end
end AnalyticNumberTheory.LargeSieve
