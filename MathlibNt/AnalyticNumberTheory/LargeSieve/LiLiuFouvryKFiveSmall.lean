import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKSupportReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKModSupportPaymentDyadic
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportReduction
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem signedError_sq_le_lowOmega_five_small_truncated_kscale
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε η : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T z = x →
      x ^ ε ≤ T z → T z ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        4 * (∑ m ∈ S, α m ^ 2) *
          wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
            (betaClean (β z) a) c a
            (fun t ↦ ((((t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η ∧
              (t.2.1.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
              (t.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x) ∧
              (t.1.1.gcd t.1.2 : ℝ) ≤ x ^ η) ∧
              ((wGCDTuple t).d₁ : ℝ) ≤ x ^ η) ∧
              ((wGCDTuple t).δ₁ : ℝ) ≤ x ^ η ∧
              ((wGCDTuple t).δ₂ : ℝ) ≤ x ^ η) +
          x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    signedError_sq_le_lowOmega_twoGCD_support_truncated_kscale
      (i := i) (j := j) (A + 2) hSW hT hN hβ hCscale hε hη,
    betaClean_wMaskedTruncated_modulus_support_dyadic_kscale Cscale hCscale i k j (A + 2) hη,
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ)]
    with x hentry hsupport hlog
  intro z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  let P : WOriginalTuple → Prop := fun t ↦
    (((t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η ∧
      (t.2.1.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
      (t.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x) ∧
      (t.1.1.gcd t.1.2 : ℝ) ≤ x ^ η) ∧
      ((wGCDTuple t).d₁ : ℝ) ≤ x ^ η
  have hg := hsupport M (T z) L hM (hT z) hL hscale hhigh hlevel
    S (N z) Q hS (hN z) hQ α (β z) c hα (hβ z) hc a hax
    (fun t ↦ P t ∧
      (x ^ η < ((wGCDTuple t).δ₁ : ℝ) ∨ x ^ η < ((wGCDTuple t).δ₂ : ℝ)))
    (fun _ _ hp ↦ hp.2)
  have hα0 : 0 ≤ ∑ m ∈ S, α m ^ 2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hgSigned :
      (∑ m ∈ S, α m ^ 2) *
        wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
          (betaClean (β z) a) c a
          (fun t ↦ P t ∧
            (x ^ η < ((wGCDTuple t).δ₁ : ℝ) ∨ x ^ η < ((wGCDTuple t).δ₂ : ℝ))) ≤
        x ^ 2 / Real.log x ^ (A + 2) :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hα0).trans hg
  have he := hentry z M L hM hL hscale hlow hhigh hlevel
    S Q hS hQ α c hα hc a ha hax
  change signedError S (N z) Q α (β z) c a ^ 2 ≤
    4 * (∑ m ∈ S, α m ^ 2) *
      wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
        (betaClean (β z) a) c a P + x ^ 2 / Real.log x ^ (A + 2) at he
  rw [wMaskedTruncated_eq_modulus_support_small_add_large M (x ^ η)
    (wUniformCutoff M (x ^ η)) (N z) Q (betaClean (β z) a) c a P] at he
  have hlog0 : 0 < Real.log x := by linarith
  have hpay : 5 * (x ^ 2 / Real.log x ^ (A + 2)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_add, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hlog0)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (show 0 ≤ Real.log x ^ 2 - 5 by nlinarith)]
  dsimp only [P] at he hgSigned
  linarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
