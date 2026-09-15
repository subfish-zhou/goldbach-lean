import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKModulusHighOmega
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorHighOmegaReduction
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem factorLowOmega_signedError_difference_payment_kscale (i k u v A : ℕ)
    {Cscale ε : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → x = 4 * M * T →
      x ^ ε ≤ T → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α β γ ζ : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ r, |γ r| ≤ (fouvryTau u r : ℝ)) →
      (∀ s, |ζ s| ≤ (fouvryTau v s : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
      |signedError S N Q α β (factorConvolution γ ζ) a -
        signedError S N Q α β
          (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) a| ≤
        x / Real.log x ^ A := by
  filter_upwards [modulusHighOmega_signedError_dyadic_log_payment_kscale i k (u + v) A hCscale hε]
    with x hpay
  intro M T L hM hT hL hscale hlow hlevel S N Q hS hN hQ α β γ ζ hα hβ hγ hζ a ha hax
  rw [signedError_sub_factorLowOmega]
  exact hpay M T L hM hT hL hscale hlow hlevel S N Q hS hN hQ
    α β (factorConvolution γ (betaHighOmega ζ (highOmegaCutoff x))) hα hβ
    (fun q _ => factorConvolution_abs_le u v γ _ hγ
      (fun s => (abs_betaHighOmega_le ζ _ s).trans (hζ s)) q)
    (fun _ _ h => factorConvolution_high_nonzero h) a ha hax


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
