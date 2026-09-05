import AnalyticNumberTheory.Mertens.Abelian
import AnalyticNumberTheory.Mertens.MangoldtBridge

/-!
# Constant identification from the prime finite part

This module closes the zeta/Euler-product side of the Mertens constant
calculation.  The only remaining analytic input is the Abelian finite-part
limit for the prime Dirichlet series.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Real

/-- Once the prime Dirichlet finite part is identified as `B - γ`, the
normalized zeta limit and the convergent Euler correction force `B + C = γ`.-/
theorem mertensConstant_eq_eulerMascheroni_of_primeFinitePart
    (hfinite : Tendsto
      (fun ε : ℝ =>
        (∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε)
      (𝓝[>] 0)
      (𝓝 (mertensSecondConstant - Real.eulerMascheroniConstant))) :
    mertensSecondConstant + logarithmicCorrectionLimit =
      Real.eulerMascheroniConstant := by
  have hadd : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) :=
        tendsto_const_nhds
      have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hc.add hi
    · filter_upwards [eventually_mem_nhdsWithin] with ε hε
      exact Set.mem_Ioi.mpr (by simpa using hε)
  have hzero : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) := by
    simpa using
      ((tendsto_id.sub (tendsto_const_nhds (x := (1 : ℝ)))).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1))
  have hzeta : Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (𝓝[>] 1) (𝓝 0) :=
    log_riemannZeta_add_log_sub_isBigO_ofReal.trans_tendsto hzero
  have hzetaε : Tendsto
      (fun ε : ℝ => Real.log (riemannZeta ((1 + ε : ℝ) : ℂ)).re + Real.log ε)
      (𝓝[>] 0) (𝓝 0) := by
    convert hzeta.comp hadd using 1 <;> simp [Function.comp_def]
  have hcorrection : Tendsto
      (fun ε : ℝ => ∑' p : Nat.Primes, primeEulerCorrection (1 + ε) p)
      (𝓝[>] 0) (𝓝 logarithmicCorrectionLimit) :=
    tendsto_tsum_primeEulerCorrection_limit.comp hadd
  have hsum := hfinite.add hcorrection
  have heq : (fun ε : ℝ =>
      ((∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε) +
        ∑' p : Nat.Primes, primeEulerCorrection (1 + ε) p) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ =>
        Real.log (riemannZeta ((1 + ε : ℝ) : ℂ)).re + Real.log ε) := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    rw [← real_primeEulerLog_eq_log_riemannZeta (by linarith : 1 < 1 + ε),
      real_primeEulerLog_decomposition (by linarith : 1 < 1 + ε)]
    ring
  have hsumzero : Tendsto
      (fun ε : ℝ =>
        ((∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε) +
          ∑' p : Nat.Primes, primeEulerCorrection (1 + ε) p)
      (𝓝[>] 0) (𝓝 0) := (tendsto_congr' heq).mpr hzetaε
  have hlimit : mertensSecondConstant - Real.eulerMascheroniConstant +
      logarithmicCorrectionLimit = 0 :=
    tendsto_nhds_unique hsum hsumzero
  linarith

end AnalyticNumberTheory.Mertens
