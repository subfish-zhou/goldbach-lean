import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaError
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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

/-- All data, including the changing residue, follow the large-`x` threshold.
The three conclusions give the deleted error, the actual original-to-trimmed
difference, and its triangle transfer. -/
theorem betaClean_highOmega_signedError_log_payment (i k j A : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ U V : ℝ,
      1 ≤ U → 1 ≤ V → U * V ≤ x → U ≤ x → V ≤ x →
      ∀ S N Q : Finset ℕ,
      S ⊆ Ioc 0 ⌊U⌋₊ → N ⊆ Ioc 0 ⌊V⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x →
      |signedError S N Q α (betaHighOmega (betaClean β a) (highOmegaCutoff x)) c a| ≤
        x / Real.log x ^ A ∧
      |signedError S N Q α (betaClean β a) c a -
        signedError S N Q α (betaLowOmega (betaClean β a) (highOmegaCutoff x)) c a| ≤
          x / Real.log x ^ A ∧
      |signedError S N Q α (betaClean β a) c a| ≤
        |signedError S N Q α (betaLowOmega (betaClean β a) (highOmegaCutoff x)) c a| +
          x / Real.log x ^ A := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    highOmega_eventually_log_payment 6 (by norm_num) (highOmegaLogExponent i k j) A]
    with x hx hpay
  intro U V hU hV hUV hUx hVx S N Q hS hN hQ α β c hα hβ hc a ha
  have hb : |signedError S N Q α
      (betaHighOmega (betaClean β a) (highOmegaCutoff x)) c a| ≤ x / Real.log x ^ A := by
    calc
      _ ≤ 6 * (2 : ℝ) ^ (-highOmegaCutoff x) * x *
          (1 + Real.log (2 * x)) ^ highOmegaLogExponent i k j :=
        betaClean_highOmega_signedError_bound i k j hU hV hx hUV hUx hVx
          S N Q hS hN hQ α β c hα hβ hc a ha (highOmegaCutoff x)
      _ = x * (6 * (2 : ℝ) ^ (-highOmegaCutoff x) *
          (1 + Real.log (2 * x)) ^ highOmegaLogExponent i k j) := by ring
      _ ≤ x * (1 / Real.log x ^ A) :=
        mul_le_mul_of_nonneg_left hpay (by linarith)
      _ = _ := by ring
  have he := signedError_eq_lowOmega_add_highOmega S N Q α (betaClean β a) c a
    (highOmegaCutoff x)
  refine ⟨hb, ?_, ?_⟩
  · rw [he, add_sub_cancel_left]
    exact hb
  · rw [he]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hb)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
