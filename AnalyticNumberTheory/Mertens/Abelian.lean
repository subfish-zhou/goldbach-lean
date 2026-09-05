import AnalyticNumberTheory.Mertens.Product
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Abelian ingredients for Mertens' product theorem

This module keeps the Euler-product continuity argument separate from the
hard-cutoff Mertens estimates.  The remaining constant-identification bridge
will use these ingredients together with an Abelian finite-part lemma.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Real

/-- The quadratic-and-higher Euler-log correction at real exponent `s`. -/
noncomputable def primeEulerCorrection (s : ℝ) (p : Nat.Primes) : ℝ :=
  -log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)

/-- Above `s = 1`, a prime Euler factor is at most one half. -/
theorem prime_rpow_neg_le_half (p : Nat.Primes) {s : ℝ} (hs : 1 < s) :
    (p : ℝ) ^ (-s) ≤ 1 / 2 := by
  calc
    (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast p.prop.one_lt.le
      · linarith
    _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      · exact_mod_cast p.prop.two_le

/-- Uniform quadratic bound for the real Euler-log correction above `s = 1`. -/
theorem norm_primeEulerCorrection_le (p : Nat.Primes) {s : ℝ} (hs : 1 < s) :
    ‖primeEulerCorrection s p‖ ≤ 2 * (p : ℝ) ^ (-2 : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have ht : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos hp _
  have htle := prime_rpow_neg_le_half p hs
  have hbase : (p : ℝ) ^ (-s) ≤ 1 / (p : ℝ) := by
    calc
      (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact_mod_cast p.prop.one_lt.le
        · linarith
      _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
  rw [primeEulerCorrection, Real.norm_eq_abs]
  calc
    |-log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)| =
        |-(log (1 - (p : ℝ) ^ (-s)) + (p : ℝ) ^ (-s))| := by
          congr 1
          ring
    _ = |log (1 - (p : ℝ) ^ (-s)) + (p : ℝ) ^ (-s)| := abs_neg _
    _ ≤ 2 * ((p : ℝ) ^ (-s)) ^ 2 := abs_log_one_sub_add_le ht htle
    _ ≤ 2 * (1 / (p : ℝ)) ^ 2 := by gcongr
    _ = 2 * (p : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hp)]
      field_simp [ne_of_gt hp]
      norm_num [Real.rpow_natCast]

/-- Each real Euler-log correction converges to its `s = 1` value. -/
theorem tendsto_primeEulerCorrection (p : Nat.Primes) :
    Tendsto (fun s : ℝ => primeEulerCorrection s p) (𝓝[>] 1)
      (𝓝 (-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hrpow : Tendsto (fun s : ℝ => (p : ℝ) ^ (-s)) (𝓝[>] 1)
      (𝓝 (1 / (p : ℝ))) := by
    have hneg : Tendsto (fun s : ℝ => -s) (𝓝 (1 : ℝ)) (𝓝 (-1 : ℝ)) :=
      continuousAt_neg.tendsto
    have hpow := (Real.continuousAt_const_rpow
      (a := (p : ℝ)) (b := (-1 : ℝ)) (ne_of_gt hp)).tendsto
    have h := hpow.comp
      (hneg.mono_left (show 𝓝[Set.Ioi (1 : ℝ)] 1 ≤ 𝓝 1 from nhdsWithin_le_nhds))
    convert h using 1 <;> simp [Function.comp_def, Real.rpow_neg_one, one_div]
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      · exact_mod_cast p.prop.two_le
    linarith
  have hlog : Tendsto (fun s : ℝ => log (1 - (p : ℝ) ^ (-s))) (𝓝[>] 1)
      (𝓝 (log (1 - 1 / (p : ℝ)))) :=
    (continuousAt_log hpos.ne').tendsto.comp ((tendsto_const_nhds.sub hrpow))
  exact (hlog.neg.sub hrpow).congr' (by rfl)

/-- The absolutely convergent Euler-log correction is continuous as `s → 1⁺`. -/
theorem tendsto_tsum_primeEulerCorrection :
    Tendsto (fun s : ℝ => ∑' p : Nat.Primes, primeEulerCorrection s p) (𝓝[>] 1)
      (𝓝 (∑' p : Nat.Primes, primeEulerCorrection 1 p)) := by
  refine tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[Set.Ioi (1 : ℝ)] 1)
    (f := fun s p => primeEulerCorrection s p)
    (g := fun p => primeEulerCorrection 1 p)
    ((Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 2) ?_ ?_
  · intro p
    simpa [primeEulerCorrection, Real.rpow_neg_one, one_div] using
      tendsto_primeEulerCorrection p
  · filter_upwards [eventually_mem_nhdsWithin] with s hs
    intro p
    exact norm_primeEulerCorrection_le p hs

/-- At `s = 1`, the prime-indexed Euler correction is the existing zero-extended
logarithmic correction constant. -/
theorem tsum_primeEulerCorrection_one :
    (∑' p : Nat.Primes, primeEulerCorrection 1 p) = logarithmicCorrectionLimit := by
  classical
  let f : ℕ → ℝ := fun n =>
    -log (1 - (n : ℝ) ^ (-(1 : ℝ))) - (n : ℝ) ^ (-(1 : ℝ))
  change (∑' (p : ↑({n : ℕ | n.Prime} : Set ℕ)), f p) = logarithmicCorrectionLimit
  rw [tsum_subtype {n : ℕ | n.Prime} f]
  simp [Set.indicator, f, logarithmicCorrectionLimit, logarithmicCorrectionTerm,
    Real.rpow_neg_one, one_div]

/-- The real Euler-log correction tends to the canonical product correction
constant as `s → 1⁺`. -/
theorem tendsto_tsum_primeEulerCorrection_limit :
    Tendsto (fun s : ℝ => ∑' p : Nat.Primes, primeEulerCorrection s p) (𝓝[>] 1)
      (𝓝 logarithmicCorrectionLimit) := by
  convert tendsto_tsum_primeEulerCorrection using 1
  rw [tsum_primeEulerCorrection_one]

/-- For a real exponent above one, the Euler logarithm splits into its prime
Dirichlet term and the uniformly convergent higher-order correction. -/
theorem real_primeEulerLog_decomposition {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, -log (1 - (p : ℝ) ^ (-s))) =
      (∑' p : Nat.Primes, (p : ℝ) ^ (-s)) +
        ∑' p : Nat.Primes, primeEulerCorrection s p := by
  have hprime : Summable fun p : Nat.Primes => (p : ℝ) ^ (-s) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hcorrection : Summable fun p : Nat.Primes => primeEulerCorrection s p := by
    refine ((Nat.Primes.summable_rpow.mpr
      (by norm_num : (-2 : ℝ) < -1)).mul_left 2).of_norm_bounded ?_
    intro p
    exact norm_primeEulerCorrection_le p hs
  rw [← hprime.tsum_add hcorrection]
  apply tsum_congr
  intro p
  simp only [primeEulerCorrection]
  ring

/-- The Gamma kernel responsible for the Euler--Mascheroni constant in the
Abelian finite-part calculation. -/
theorem complex_integral_log_mul_exp_eq_neg_eulerMascheroni :
    (∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ ((1 : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      (-Real.eulerMascheroniConstant : ℂ) := by
  let I : ℂ := ∫ t : ℝ in Set.Ioi 0,
    (t : ℂ) ^ ((1 : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))
  let D₁ : ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.toSpanSingleton ℂ I).restrictScalars ℝ |>.comp Complex.ofRealCLM
  let D₂ : ℝ →L[ℝ] ℂ := Complex.ofRealCLM.comp
    (ContinuousLinearMap.toSpanSingleton ℝ (-Real.eulerMascheroniConstant))
  have h₁ : HasFDerivAt (fun x : ℝ => Complex.GammaIntegral (x : ℂ)) D₁ 1 := by
    simpa [D₁, I, Function.comp_def] using
      ((((Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)).hasFDerivAt).restrictScalars ℝ).comp 1
        Complex.ofRealCLM.hasFDerivAt)
  have heq : (fun x : ℝ => Complex.GammaIntegral (x : ℂ)) =ᶠ[𝓝 1]
      fun x => (Real.Gamma x : ℂ) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [← Complex.Gamma_eq_integral (by simpa using hx), Complex.Gamma_ofReal]
  have h₂raw : HasFDerivAt (fun x : ℝ => (Real.Gamma x : ℂ)) D₂ 1 := by
    simpa [D₂, Function.comp_def] using
      (Complex.ofRealCLM.hasFDerivAt.comp 1 Real.hasDerivAt_Gamma_one.hasFDerivAt)
  have h₂ : HasFDerivAt (fun x : ℝ => Complex.GammaIntegral (x : ℂ)) D₂ 1 :=
    (heq.hasFDerivAt_iff).mpr h₂raw
  have hD : D₁ = D₂ := h₁.unique h₂
  have hval := congrArg (fun D : ℝ →L[ℝ] ℂ => D 1) hD
  simpa [D₁, D₂, I] using hval

/-- Simplified Gamma kernel form used by the Mellin finite-part calculation. -/
theorem complex_integral_log_exp_eq_neg_eulerMascheroni :
    (∫ t : ℝ in Set.Ioi 0, (Real.log t : ℂ) * (Real.exp (-t) : ℂ)) =
      (-Real.eulerMascheroniConstant : ℂ) := by
  convert complex_integral_log_mul_exp_eq_neg_eulerMascheroni using 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp

end AnalyticNumberTheory.Mertens
