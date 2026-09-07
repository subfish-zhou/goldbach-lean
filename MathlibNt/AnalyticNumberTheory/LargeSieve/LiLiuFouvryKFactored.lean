import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKFiveSmall
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKFactorDifference
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryExtendedPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorHighOmegaReduction
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem signedError_sq_le_five_small_factored_kscale
    {ι : Type*} {κ k i u v : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε η : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M L R₀ S₀ : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T z = x →
      x ^ ε ≤ T z → T z ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c γ ζ : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ r, |γ r| ≤ (fouvryTau u r : ℝ)) →
      (∀ s, |ζ s| ≤ (fouvryTau v s : ℝ)) →
      factorSupported R₀ γ → factorSupported S₀ ζ → c = factorConvolution γ ζ →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        8 * (∑ m ∈ S, α m ^ 2) *
          wMaskedFactoredTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
            (betaClean (β z) a)
            (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
            γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) +
          x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    signedError_sq_le_lowOmega_five_small_truncated_kscale
      (i := i) (j := u + v) (A + 2) hSW hT hN hβ hCscale hε hη,
    factorLowOmega_signedError_difference_payment_kscale i k u v (A + 2) hCscale hε,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with x hentry hdiff hlog
  intro z M L R₀ S₀ hM hL hscale hlow hhigh hlevel S Q hS hQ α c γ ζ
    hα hγ hζ hγs hζs hc a ha hax
  let c' := factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))
  have hc' (q : ℕ) : |c' q| ≤ (fouvryTau (u + v) q : ℝ) :=
    factorConvolution_abs_le u v γ _ hγ
      (fun s => (abs_betaLowOmega_le ζ _ s).trans (hζ s)) q
  have he := hentry z M L hM hL hscale hlow hhigh hlevel
    S Q hS hQ α c' hα (fun q _ => hc' q) a ha hax
  change signedError S (N z) Q α (β z) c' a ^ 2 ≤
    4 * (∑ m ∈ S, α m ^ 2) *
      wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
        (betaClean (β z) a) c' a (c2FiveSmallMask x η) +
      x ^ 2 / Real.log x ^ (A + 2) at he
  rw [wMaskedTruncated_eq_factored_of_eq hγs hζs rfl] at he
  have hd := hdiff M (T z) L hM (hT z) hL hscale.symm hlow hlevel
    S (N z) Q hS (hN z) hQ α (β z) γ ζ hα (hβ z) hγ hζ a ha hax
  rw [← hc] at hd
  have hlog0 : 0 < Real.log x := by linarith
  have hp : 1 ≤ Real.log x ^ (A + 2) := one_le_pow₀ (by linarith)
  have hdSq :
      (signedError S (N z) Q α (β z) c a -
        signedError S (N z) Q α (β z) c' a) ^ 2 ≤
          x ^ 2 / Real.log x ^ (A + 2) := by
    calc
      _ ≤ (x / Real.log x ^ (A + 2)) ^ 2 :=
        sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2
      _ = x ^ 2 / (Real.log x ^ (A + 2)) ^ 2 := div_pow _ _ _
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg x) (by positivity)
        (by nlinarith)
  have hpay : 4 * (x ^ 2 / Real.log x ^ (A + 2)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_add, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hlog0)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (show 0 ≤ Real.log x ^ 2 - 4 by nlinarith)]
  have hsquare :
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        2 * signedError S (N z) Q α (β z) c' a ^ 2 +
        2 * (signedError S (N z) Q α (β z) c a -
          signedError S (N z) Q α (β z) c' a) ^ 2 := by
    nlinarith [sq_nonneg (signedError S (N z) Q α (β z) c a -
      2 * signedError S (N z) Q α (β z) c' a)]
  change signedError S (N z) Q α (β z) c a ^ 2 ≤
    8 * (∑ m ∈ S, α m ^ 2) *
      wMaskedFactoredTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
        (betaClean (β z) a) c' γ ζ a (c2FiveSmallMask x η)
        R₀ S₀ (highOmegaCutoff x) + x ^ 2 / Real.log x ^ A
  linarith

/-- Choose a legal split of the original WF level and feed the resulting
factors into the actual retained W. Factors are chosen before the residue.
This is preprocessing, not the missing IV.3 estimate of the displayed W. -/
theorem wellFactorable_signedError_sq_le_five_small_factored_kscale
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε η : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4 * M * T z = x →
      ε ≤ ν → ν ≤ 1 / 10+ε/10 → T z = x ^ ν →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊ →
      ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      SignedWellFactorable j (x ^ ((5 - 5 * ν) / 9 - ε)) c →
      let R₀ := x ^ c2RExponent ν ε
      let S₀ := x ^ c2SExponent ν ε
      R₀ * S₀ = x ^ ((5 - 5 * ν) / 9 - ε) ∧
        ∃ γ ζ : ℕ → ℝ,
          factorSupported R₀ γ ∧ factorSupported S₀ ζ ∧
          (∀ r, |γ r| ≤ (fouvryTau j r : ℝ)) ∧
          (∀ s, |ζ s| ≤ (fouvryTau j s : ℝ)) ∧ c = factorConvolution γ ζ ∧
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
          signedError S (N z) Q α (β z) c a ^ 2 ≤
            8 * (∑ m ∈ S, α m ^ 2) *
              wMaskedFactoredTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
                (betaClean (β z) a)
                (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) +
              x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    signedError_sq_le_five_small_factored_kscale
      (i := i) (u := j) (v := j) A hSW hT hN hβ hCscale hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hentry hx
  intro z M ν hM hscale hεν hν hpower S Q hS hQ α c hα hWF
  obtain ⟨hR, hS₀, hRS, _⟩ := c2_extended_factor_levels hx hε hεν hν
  obtain ⟨γ, ζ, hγs, hζs, hγ, hζ, hc⟩ := hWF.2 _ _ hR hS₀ hRS
  refine ⟨hRS, γ, ζ, hγs, hζs, hγ, hζ, hc, ?_⟩
  intro a ha hax
  have hL : 1 ≤ x ^ ((5 - 5 * ν) / 9 - ε) := by
    rw [← hRS]
    nlinarith
  have hlevel : x ^ ((5 - 5 * ν) / 9 - ε) ≤ x ^ (5 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hlow : x ^ ε ≤ T z := by
    rw [hpower]
    exact Real.rpow_le_rpow_of_exponent_le hx hεν
  have hhigh : T z ≤ x ^ (1 / 9 : ℝ) := by
    rw [hpower]
    exact Real.rpow_le_rpow_of_exponent_le hx (c2_extended_parameter_caps hεν hν).2
  exact hentry z M _ _ _ hM hL hscale hlow hhigh hlevel
    S Q hS hQ α c γ ζ hα hγ hζ hγs hζs hc a ha hax


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
