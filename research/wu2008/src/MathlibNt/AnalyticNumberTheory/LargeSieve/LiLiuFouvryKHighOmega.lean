import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDivisor
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaPayment
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem betaClean_highOmega_signedError_bound_kscale (i k j : ℕ) {Cscale : ℝ} (hCscale : 1 ≤ Cscale)
    {U V x : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hUV : U * V ≤ x) (hUx : U ≤ x) (hVx : V ≤ x)
    (S N Q : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊U⌋₊)
    (hN : N ⊆ Ioc 0 ⌊V⌋₊) (hQ : Q ⊆ Ioc 0 ⌊x⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ Cscale*x) (ξ : ℝ) :
    |signedError S N Q α (betaHighOmega (betaClean β a) ξ) c a| ≤
      (6*Cscale*(1+Real.log Cscale)^highOmegaLogExponent i k j) * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ highOmegaLogExponent i k j := by
  have hxx : x ≤ Cscale*x := le_mul_of_one_le_left (by linarith) hCscale
  have hh := betaClean_highOmega_signedError_bound i k j hU hV (hx.trans hxx)
    (hUV.trans hxx) (hUx.trans hxx) (hVx.trans hxx) S N Q hS hN
    (hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hxx))) α β c hα hβ hc a ha ξ
  have hl := kscale_log_cost hCscale hx (highOmegaLogExponent i k j)
  calc
    _ ≤ 6*(2 : ℝ)^(-ξ)*(Cscale*x)*
        (1+Real.log (2*Cscale*x))^highOmegaLogExponent i k j := by
      simpa only [mul_assoc] using hh
    _ ≤ 6*(2 : ℝ)^(-ξ)*(Cscale*x)*
        ((1+Real.log Cscale)^highOmegaLogExponent i k j *
          (1+Real.log (2*x))^highOmegaLogExponent i k j) := by gcongr
    _ = _ := by ring

theorem betaClean_highOmega_signedError_log_payment_kscale (i k j A : ℕ)
    {Cscale : ℝ} (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ U V : ℝ,
      1 ≤ U → 1 ≤ V → U * V ≤ x → U ≤ x → V ≤ x →
      ∀ S N Q : Finset ℕ,
      S ⊆ Ioc 0 ⌊U⌋₊ → N ⊆ Ioc 0 ⌊V⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale*x →
      |signedError S N Q α (betaHighOmega (betaClean β a) (highOmegaCutoff x)) c a| ≤
        x / Real.log x ^ A ∧
      |signedError S N Q α (betaClean β a) c a -
        signedError S N Q α (betaLowOmega (betaClean β a) (highOmegaCutoff x)) c a| ≤
          x / Real.log x ^ A ∧
      |signedError S N Q α (betaClean β a) c a| ≤
        |signedError S N Q α (betaLowOmega (betaClean β a) (highOmegaCutoff x)) c a| +
          x / Real.log x ^ A := by
  have hlogC := Real.log_nonneg hCscale
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    highOmega_eventually_log_payment (6*Cscale*(1+Real.log Cscale)^highOmegaLogExponent i k j) (by positivity) (highOmegaLogExponent i k j) A]
    with x hx hpay
  intro U V hU hV hUV hUx hVx S N Q hS hN hQ α β c hα hβ hc a ha
  have hb : |signedError S N Q α
      (betaHighOmega (betaClean β a) (highOmegaCutoff x)) c a| ≤ x / Real.log x ^ A := by
    calc
      _ ≤ (6*Cscale*(1+Real.log Cscale)^highOmegaLogExponent i k j) * (2 : ℝ) ^ (-highOmegaCutoff x) * x *
          (1 + Real.log (2 * x)) ^ highOmegaLogExponent i k j :=
        betaClean_highOmega_signedError_bound_kscale i k j hCscale hU hV hx hUV hUx hVx
          S N Q hS hN hQ α β c hα hβ hc a ha (highOmegaCutoff x)
      _ = x * ((6*Cscale*(1+Real.log Cscale)^highOmegaLogExponent i k j) * (2 : ℝ) ^ (-highOmegaCutoff x) *
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
