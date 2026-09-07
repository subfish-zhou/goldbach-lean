import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKCleanReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKLargeGCDBetaClean
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanFirstGCD
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem signedError_sq_le_clean_firstGCD_truncated_kscale
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
        2 * (∑ m ∈ S, α m ^ 2) *
          wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
            (betaClean (β z) a) c a
            (fun t ↦ (t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η) +
          x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    kClean_signedError_sq_le_clean_nonzeroMode_c2 (i := i) (j := j) (A + 2) hSW hT hN hβ hCscale hε,
    wMaskedTail_uniformCutoff_alpha_log_payment i k j (A + 2) hη,
    betaClean_wMaskedTruncated_largeGCD_dyadic_kscale i k j (A + 2 : ℕ) hη hCscale,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ)]
    with x hentry htail hlarge hx hlog
  intro z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  have hM0 : 0 < M := by linarith
  have hMx : 2 * M ≤ x := by nlinarith [hT z]
  have hTx : 2 * T z ≤ x := by nlinarith [hT z]
  have hLx : L ≤ x := hlevel.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hSx : S ⊆ Ioc 0 ⌊x⌋₊ := by
    intro m hm
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor ((hS m hm).2.trans hMx)⟩
    have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
    exact_mod_cast this
  have hNx : N z ⊆ Ioc 0 ⌊x⌋₊ := by
    intro n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor ((hN z n hn).2.trans hTx)⟩
    have : (0 : ℝ) < n := by have := (hN z n hn).1; have := hT z; linarith
    exact_mod_cast this
  have hQx : Q ⊆ Ioc 0 ⌊x⌋₊ :=
    hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hLx))
  have hcleanβ : ∀ n ∈ N z, |betaClean (β z) a n| ≤ (fouvryTau k n : ℝ) :=
    fun n hn ↦ (abs_betaClean_le _ _ _).trans (hβ z n hn)
  have ht := htail M hM0 S (N z) Q hSx hNx hQx α (betaClean (β z) a) c
    hα hcleanβ hc a (fun _ ↦ True)
  have hg := (hlarge M (T z) L hM (hT z) hL hscale hlevel S (N z) Q
    hS (hN z) hQ α (β z) c hα (hβ z) hc a hax
    (fun t ↦ x ^ η < (t.2.1.gcd t.2.2 : ℝ)) (fun _ _ hp ↦ hp)).2
  simp only [Real.rpow_natCast] at hg
  have hα0 : 0 ≤ ∑ m ∈ S, α m ^ 2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have htSigned :
      (∑ m ∈ S, α m ^ 2) *
        wMaskedTail M (wUniformCutoff M (x ^ η)) (N z) Q
          (betaClean (β z) a) c a (fun _ ↦ True) ≤ x ^ 2 / Real.log x ^ (A + 2) :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hα0).trans ht
  have hgSigned :
      (∑ m ∈ S, α m ^ 2) *
        wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
          (betaClean (β z) a) c a
          (fun t ↦ x ^ η < (t.2.1.gcd t.2.2 : ℝ)) ≤ x ^ 2 / Real.log x ^ (A + 2) :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hα0).trans hg
  have he := hentry z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  rw [smoothWNonzeroMode_eq_firstGCD_small_add_large_add_tail
    M (x ^ η) (wUniformCutoff M (x ^ η)) (N z) Q (betaClean (β z) a) c a] at he
  have hlog0 : 0 < Real.log x := by linarith
  have hpay : 5 * (x ^ 2 / Real.log x ^ (A + 2)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_add, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hlog0)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (show 0 ≤ Real.log x ^ 2 - 5 by nlinarith)]
  linarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
