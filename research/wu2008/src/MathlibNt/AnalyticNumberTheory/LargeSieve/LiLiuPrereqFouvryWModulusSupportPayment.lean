import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanTail

/-!
# Power saving for both supported modulus factors

The square-divisor saving pays the fixed-order divisor losses and logarithms.
The original progression endpoint is absorbed under `L ≤ M`; this condition
will be derived, not assumed, at the C.2 dyadic scale.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The same arbitrary submask is used for the original sum and its zero mode.
Here `T` is the upper beta endpoint, and the threshold is uniform in all
changing scales, residue, supports, signed coefficients, and masks. -/
theorem eventually_wMaskedOriginal_zero_modulus_support_power_saving
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → M * T ≤ x → L ≤ M →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t →
        x ^ η < ((wGCDTuple t).δ₁ : ℝ) ∨ x ^ η < ((wGCDTuple t).δ₂ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| ≤
        2 * M * T ^ 2 * x ^ (-η / 4) := by
  obtain ⟨C, hC, hOriginal⟩ :=
    wMaskedOriginal_abs_le_modulus_support j (show 0 < η / 8 by linarith)
  obtain ⟨D, hD, hZero⟩ :=
    wMaskedZeroMode_abs_le_modulus_support j (show 0 < η / 8 by linarith)
  let p := (k - 1) * 2
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    betaPayment_eventually_log_mul_rpow_le (2 * C) (by positivity) (p + 1)
      (b := η / 8 - η / 2) (d := -η / 4) (by linarith),
    betaPayment_eventually_log_mul_rpow_le (D * |dyadicCutoffMass|)
      (by positivity) (p + 2) (b := η / 8 - η / 2) (d := -η / 4) (by linarith)]
    with x hx hpayOriginal hpayZero
  intro M T L hM hT hL hMT hLM N Q hN hQ β c hβ hc a ha hs P hP
  have hx0 : 0 < x := by linarith
  have hMx : M ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ M) hT).trans hMT
  have hTx : T ≤ x := (le_mul_of_one_le_left (by linarith : 0 ≤ T) hM).trans hMT
  have hLx : L ≤ x := hLM.trans hMx
  let H := 1 + Real.log x
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hx]
  have hHT0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have hHL0 : 0 ≤ 1 + Real.log L := by linarith [Real.log_nonneg hL]
  have hHT : 1 + Real.log T ≤ H := by
    dsimp [H]
    linarith [Real.log_le_log (by linarith : 0 < T) hTx]
  have hHL : 1 + Real.log L ≤ H := by
    dsimp [H]
    linarith [Real.log_le_log (by linarith : 0 < L) hLx]
  have hB : (∑ n ∈ N, |β n|) ^ 2 ≤ T ^ 2 * H ^ p := by
    calc
      _ ≤ (T * (1 + Real.log T) ^ (k - 1)) ^ 2 :=
        pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ abs_nonneg _))
          (sum_abs_le_fouvryTau_mean hk hT N hN β hβ) 2
      _ ≤ (T * H ^ (k - 1)) ^ 2 := by
        gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hroot : Real.sqrt (x ^ η) = x ^ (η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hlength : M * (1 + Real.log L) + L ≤ 2 * M * H := by
    have := mul_le_mul_of_nonneg_left hHL (by linarith : 0 ≤ M)
    have := mul_le_mul_of_nonneg_left hH (by linarith : 0 ≤ M)
    nlinarith
  have hO : |wMaskedOriginal M N Q β c a P| ≤ M * T ^ 2 * x ^ (-η / 4) := by
    calc
      _ ≤ C * x ^ (η / 8) * (M * (1 + Real.log L) + L) *
          (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt (x ^ η) :=
        hOriginal M T L x (x ^ η) hM hT hL hMT hLx
          (Real.rpow_pos_of_pos hx0 _) N Q hN hQ β c hc a ha hs P hP
      _ ≤ C * x ^ (η / 8) * (2 * M * H) *
          (T ^ 2 * H ^ p) / Real.sqrt (x ^ η) := by gcongr
      _ = M * T ^ 2 * (2 * C * H ^ (p + 1) * x ^ (η / 8 - η / 2)) := by
        rw [hroot, Real.rpow_sub hx0, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpayOriginal (by positivity)
  have hZ : |wMaskedZeroMode M N Q β c a P| ≤ M * T ^ 2 * x ^ (-η / 4) := by
    calc
      _ ≤ D * |M * dyadicCutoffMass| * x ^ (η / 8) *
          (∑ n ∈ N, |β n|) ^ 2 * (1 + Real.log L) ^ 2 / Real.sqrt (x ^ η) :=
        hZero L x (x ^ η) hL hLx (Real.rpow_pos_of_pos hx0 _)
          M N Q hQ β c hc a P hP
      _ ≤ D * (M * |dyadicCutoffMass|) * x ^ (η / 8) *
          (T ^ 2 * H ^ p) * H ^ 2 / Real.sqrt (x ^ η) := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ M)]
        gcongr
      _ = M * T ^ 2 *
          (D * |dyadicCutoffMass| * H ^ (p + 2) * x ^ (η / 8 - η / 2)) := by
        rw [hroot, Real.rpow_sub hx0, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpayZero (by positivity)
  linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
