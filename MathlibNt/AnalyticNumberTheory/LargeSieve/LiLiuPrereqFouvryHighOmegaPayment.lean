import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaError

/-!
# Payment at the growing cutoff `(log x)^(1/5)`

The threshold depends only on fixed orders and the requested logarithmic
saving. It precedes all changing scales, supports, coefficients and residues.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def highOmegaCutoff (x : ℝ) : ℝ := Real.log x ^ (1 / 5 : ℝ)

theorem highOmega_eventually_log_payment (K : ℝ) (hK : 0 ≤ K) (B A : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      K * (2 : ℝ) ^ (-highOmegaCutoff x) * (1 + Real.log (2 * x)) ^ B ≤
        1 / Real.log x ^ A := by
  let C : ℝ := 2 + Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; linarith
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop (5 * (A + B)) hlog2).const_mul_left
    (K * C ^ B)).bound (show (0 : ℝ) < 1 by norm_num)
  have ht : Tendsto highOmegaCutoff atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 5 by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hb hx hlog
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hpower : highOmegaCutoff x ^ (5 * (A + B)) = Real.log x ^ (A + B) := by
    dsimp [highOmegaCutoff]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    have he : (1 / 5 : ℝ) * ((5 * (A + B) : ℕ) : ℝ) = ((A + B : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
  have hb' : K * C ^ B * Real.log x ^ (A + B) ≤ (2 : ℝ) ^ highOmegaCutoff x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, hpower] using hb
  have hH : 0 ≤ 1 + Real.log (2 * x) := by
    have := Real.log_nonneg (show 1 ≤ 2 * x by linarith)
    linarith
  have hHle : 1 + Real.log (2 * x) ≤ C * Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    dsimp [C]
    nlinarith
  have htotal : K * (1 + Real.log (2 * x)) ^ B * Real.log x ^ A ≤
      (2 : ℝ) ^ highOmegaCutoff x := by
    calc
      _ ≤ K * (C * Real.log x) ^ B * Real.log x ^ A := by gcongr
      _ = K * C ^ B * Real.log x ^ (A + B) := by rw [mul_pow, pow_add]; ring
      _ ≤ _ := hb'
  apply (le_div_iff₀ (pow_pos hl0 A)).mpr
  calc
    _ = (2 : ℝ) ^ (-highOmegaCutoff x) *
        (K * (1 + Real.log (2 * x)) ^ B * Real.log x ^ A) := by ring
    _ ≤ (2 : ℝ) ^ (-highOmegaCutoff x) * (2 : ℝ) ^ highOmegaCutoff x :=
      mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg (by norm_num) _)
    _ = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp

theorem signedError_eq_lowOmega_add_highOmega
    (S N Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) (ξ : ℝ) :
    signedError S N Q α β c a =
      signedError S N Q α (betaLowOmega β ξ) c a +
        signedError S N Q α (betaHighOmega β ξ) c a := by
  conv_lhs => arg 5; ext n; rw [beta_eq_lowOmega_add_highOmega β ξ n]
  exact signedError_add_beta S N Q α _ _ c a


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
