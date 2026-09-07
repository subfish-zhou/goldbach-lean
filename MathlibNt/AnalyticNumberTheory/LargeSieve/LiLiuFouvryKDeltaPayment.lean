import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDeltaOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanTail

/-!
# Power payment for the same large-common-modulus mask

Here `T` is the upper beta endpoint. The saving depends on a positive lower
power bound for both lengths, not just on the common-modulus threshold.
The original progression sum and its zero mode keep exactly the same mask.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem kDelta_length_payment {x U ρ η : ℝ}
    (hx : 1 ≤ x) (hU : 0 ≤ U) (hlow : x ^ ρ ≤ U) (hρη : ρ ≤ η) :
    1 ≤ U * x ^ (-ρ) ∧ U / x ^ η + 1 ≤ 2 * U * x ^ (-ρ) := by
  have hx0 : 0 < x := by linarith
  have hcancel : x ^ ρ * x ^ (-ρ) = 1 := by
    rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
  have hone : 1 ≤ U * x ^ (-ρ) := by
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hx0.le _)
  refine ⟨hone, ?_⟩
  have hdiv : U / x ^ η ≤ U * x ^ (-ρ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hU
  linarith

/-- The original and zero-mode terms are paid together on an arbitrary
submask of the large common-modulus condition. The threshold is uniform in
all changing data. The positive beta order is removed in the dyadic API. -/
theorem eventually_wMaskedOriginal_zero_largeDelta_power_saving_kscale
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ρ η Cscale : ℝ}
    (hρ : 0 < ρ) (hρη : ρ ≤ η) (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x → x ^ ρ ≤ M → x ^ ρ ≤ T →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.1.1.gcd t.1.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| ≤
        2 * M * T ^ 2 * x ^ (-ρ / 2) := by
  obtain ⟨C, hC, hb⟩ :=
    wMaskedOriginal_abs_le_largeDelta_kscale hk j (show 0 < ρ / 4 by linarith) hCscale
  let p := k ^ 2 - 1 + 2 * (k - 1)
  let s := 2 * j ^ 2 + 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    betaPayment_eventually_log_mul_rpow_le (3 * C) (by positivity) p
      (b := ρ / 4 - ρ) (d := -ρ / 2) (by linarith),
    betaPayment_eventually_log_mul_rpow_le (2 * |dyadicCutoffMass|) (by positivity)
      (k ^ 2 - 1 + s) (b := -ρ) (d := -ρ / 2) (by linarith)]
    with x hx hpayOriginal hpayZero
  intro M T hM hT hMT hρM hρT N Q hN hQ β c hβ hc a ha hs P hP
  have hx0 : 0 < x := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTx : T ≤ x := (le_mul_of_one_le_left hT0 hM).trans hMT
  let H := 1 + Real.log x
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hx]
  have hHT0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have hHT : 1 + Real.log T ≤ H := by
    dsimp [H]
    linarith [Real.log_le_log (by linarith : 0 < T) hTx]
  have hPa : (1 + Real.log T) ^ (k ^ 2 - 1) ≤ H ^ p :=
    (pow_le_pow_left₀ hHT0 hHT _).trans (pow_le_pow_right₀ hH (by dsimp [p]; omega))
  have hPb : ((1 + Real.log T) ^ (k - 1)) ^ 2 ≤ H ^ p := by
    rw [← pow_mul]
    exact (pow_le_pow_left₀ hHT0 hHT _).trans
      (pow_le_pow_right₀ hH (by dsimp [p]; omega))
  have hMp := kDelta_length_payment hx hM0 hρM hρη
  have hTp := kDelta_length_payment hx hT0 hρT hρη
  have hdiag : M * T ≤ M * T ^ 2 * x ^ (-ρ) := by
    have := mul_le_mul_of_nonneg_left hTp.1 (mul_nonneg hM0 hT0)
    nlinarith
  have hO :
      |wMaskedOriginal M N Q β c a P| ≤ M * T ^ 2 * x ^ (-ρ / 2) := by
    calc
      _ ≤ C * x ^ (ρ / 4) *
          (M * T * (1 + Real.log T) ^ (k ^ 2 - 1) +
            (M / x ^ η + 1) * (T * (1 + Real.log T) ^ (k - 1)) ^ 2) :=
        hb M T x hM hT hx hMT N Q hN β c hβ hc a ha hs (x ^ η)
          (Real.rpow_pos_of_pos hx0 _) P hP
      _ ≤ C * x ^ (ρ / 4) *
          ((M * T ^ 2 * x ^ (-ρ)) * H ^ p +
            (2 * M * x ^ (-ρ)) * (T ^ 2 * H ^ p)) := by
        rw [mul_pow]
        gcongr
        exact hMp.2
      _ = M * T ^ 2 * (3 * C * H ^ p * x ^ (ρ / 4 - ρ)) := by
        rw [Real.rpow_sub hx0, Real.rpow_neg hx0.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpayOriginal (by positivity)
  have hZ :
      |wMaskedZeroMode M N Q β c a P| ≤ M * T ^ 2 * x ^ (-ρ / 2) := by
    calc
      _ ≤ |M * dyadicCutoffMass| *
          ((T / x ^ η + 1) * (T * (1 + Real.log T) ^ (k ^ 2 - 1))) *
            H ^ s :=
        wMaskedZeroMode_abs_le_largeDelta hk j hT hx
          (Real.rpow_pos_of_pos hx0 _) M N Q hN hQ β c hβ hc a P hP
      _ = M * |dyadicCutoffMass| *
          ((T / x ^ η + 1) * (T * (1 + Real.log T) ^ (k ^ 2 - 1))) *
            H ^ s := by rw [abs_mul, abs_of_nonneg hM0]
      _ ≤ M * |dyadicCutoffMass| *
          ((2 * T * x ^ (-ρ)) * (T * H ^ (k ^ 2 - 1))) * H ^ s := by
        gcongr
        exact hTp.2
      _ = M * T ^ 2 *
          (2 * |dyadicCutoffMass| * H ^ (k ^ 2 - 1 + s) * x ^ (-ρ)) := by
        rw [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpayZero (by positivity)
  linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
