import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaPaymentDyadic

/-!
# The original C.2 error with both gcd restrictions

The low-omega, first-small-beta-gcd tuple domain is partitioned by the common
modulus. Its large part is paid using its own original sum, zero mode and tail.
The retained signed sum has the same coefficients, phases and frequency cutoff.
The three remaining support-factor exclusions and IV.3 are not asserted here.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- An exact partition inside any existing arithmetic mask. -/
theorem wMaskedTruncated_eq_delta_small_add_large
    (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q β c a P =
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ (t.1.1.gcd t.1.2 : ℝ) ≤ Y) +
      wMaskedTruncated M H N Q β c a
        (fun t ↦ P t ∧ Y < (t.1.1.gcd t.1.2 : ℝ)) := by
  simp only [wMaskedTruncated, wMaskedTuples, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hp : P t <;> by_cases hd : (t.1.1.gcd t.1.2 : ℝ) ≤ Y <;>
    simp [hp, hd, not_lt_of_ge, lt_of_not_ge]

/-- The original signed error, with no nondivisibility premise on beta,
reduced to low-omega tuples with both beta gcd and modulus gcd small.
All orders may be zero; the SW constants still precede the changing family
index, scales and residue. No closure of WF weights under masks is used. -/
theorem signedError_sq_le_lowOmega_twoGCD_truncated_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T z = x →
      x ^ ε ≤ T z → T z ≤ x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        4 * (∑ m ∈ S, α m ^ 2) *
          wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
            (betaClean (β z) a) c a
            (fun t ↦ ((t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η ∧
              (t.2.1.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
              (t.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x) ∧
              (t.1.1.gcd t.1.2 : ℝ) ≤ x ^ η) +
          x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    signedError_sq_le_lowOmega_firstGCD_truncated_c2
      (i := i) (j := j) (A + 2) hSW hT hN hβ hε hη,
    betaClean_wMaskedTruncated_largeDelta_dyadic i k j (A + 2) hε hη,
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ)]
    with x hentry hdelta hlog
  intro z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  let P : WOriginalTuple → Prop := fun t ↦
    (t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η ∧
      (t.2.1.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
      (t.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x
  have hg := hdelta M (T z) L hM (hT z) hL hscale hlow hhigh hlevel
    S (N z) Q hS (hN z) hQ α (β z) c hα (hβ z) hc a hax
    (fun t ↦ P t ∧ x ^ η < (t.1.1.gcd t.1.2 : ℝ))
    (fun _ _ hp ↦ hp.2)
  have hα0 : 0 ≤ ∑ m ∈ S, α m ^ 2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hgSigned :
      (∑ m ∈ S, α m ^ 2) *
        wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
          (betaClean (β z) a) c a
          (fun t ↦ P t ∧ x ^ η < (t.1.1.gcd t.1.2 : ℝ)) ≤
        x ^ 2 / Real.log x ^ (A + 2) :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hα0).trans hg
  have he := hentry z M L hM hL hscale hlow hhigh hlevel
    S Q hS hQ α c hα hc a ha hax
  rw [wMaskedTruncated_eq_delta_small_add_large M (x ^ η)
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
