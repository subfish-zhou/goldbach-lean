import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeSupportBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanTail

/-!
# Power payment for a large canonical supported beta factor

Here `T` is the upper beta endpoint. The sparse square-divisor envelope
saves `x ^ (-η / 4)` before paying the divisor loss and logarithms.
The original sum and zero mode retain the same arbitrary mask, and neither
length requires a positive power lower bound.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem largeSupport_sqrt_rpow {x : ℝ} (hx : 0 < x) (η : ℝ) :
    Real.sqrt (2 / Real.sqrt (x ^ η)) = Real.sqrt 2 * x ^ (-η / 4) := by
  have hp : Real.sqrt (Real.sqrt (x ^ η)) = x ^ (η / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [Real.sqrt_div (by norm_num), hp, div_eq_mul_inv, ← Real.rpow_neg hx.le]
  congr 2
  ring

/-- Uniform power saving for the original and zero-mode terms on every
submask of the large canonical `d₁` condition. The threshold precedes all
changing data; nondivisibility is later supplied by `betaClean`. -/
theorem eventually_wMaskedOriginal_zero_largeSupport_power_saving
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t →
        x ^ η < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| ≤
        2 * M * T ^ 2 * x ^ (-η / 8) := by
  obtain ⟨C, hC, hb⟩ :=
    wMaskedOriginal_abs_le_largeSupport hk j (show 0 < η / 16 by linarith)
  let p := k ^ 2 - 1
  let s := 2 * j ^ 2 + 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    betaPayment_eventually_log_mul_rpow_le (C * Real.sqrt 2) (by positivity) p
      (b := η / 16 - η / 4) (d := -η / 8) (by linarith),
    betaPayment_eventually_log_mul_rpow_le (|dyadicCutoffMass| * Real.sqrt 2)
      (by positivity) (p + s) (b := -η / 4) (d := -η / 8) (by linarith)]
    with x hx hpayOriginal hpayZero
  intro M T hM hT hMT N Q hN hQ β c hβ hc a ha hs P hP
  have hx0 : 0 < x := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTx : T ≤ x := (le_mul_of_one_le_left hT0 hM).trans hMT
  let H := 1 + Real.log x
  have hH : 0 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hx]
  have hHT0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have hHT : 1 + Real.log T ≤ H := by
    dsimp [H]
    linarith [Real.log_le_log (by linarith : 0 < T) hTx]
  have hO :
      |wMaskedOriginal M N Q β c a P| ≤ M * T ^ 2 * x ^ (-η / 8) := by
    calc
      _ ≤ C * M * x ^ (η / 16) *
          (T ^ 2 * (1 + Real.log T) ^ p *
            Real.sqrt (2 / Real.sqrt (x ^ η))) :=
        hb M T (x ^ η) x hM hT (Real.rpow_pos_of_pos hx0 _) hx hMT
          N Q hN β c hβ hc a ha hs P hP
      _ ≤ C * M * x ^ (η / 16) *
          (T ^ 2 * H ^ p * (Real.sqrt 2 * x ^ (-η / 4))) := by
        rw [largeSupport_sqrt_rpow hx0]
        gcongr
      _ = M * T ^ 2 *
          (C * Real.sqrt 2 * H ^ p * x ^ (η / 16 - η / 4)) := by
        rw [Real.rpow_sub hx0, show -η / 4 = -(η / 4) by ring,
          Real.rpow_neg hx0.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpayOriginal (by positivity)
  have hZ :
      |wMaskedZeroMode M N Q β c a P| ≤ M * T ^ 2 * x ^ (-η / 8) := by
    calc
      _ ≤ |M * dyadicCutoffMass| *
          (T ^ 2 * (1 + Real.log T) ^ p *
            Real.sqrt (2 / Real.sqrt (x ^ η))) * H ^ s :=
        wMaskedZeroMode_abs_le_largeSupport hk j hT hx
          (Real.rpow_pos_of_pos hx0 _) M N Q hN hQ β c hβ hc a P hP
      _ = M * |dyadicCutoffMass| *
          (T ^ 2 * (1 + Real.log T) ^ p *
            (Real.sqrt 2 * x ^ (-η / 4))) * H ^ s := by
        rw [abs_mul, abs_of_nonneg hM0, largeSupport_sqrt_rpow hx0]
      _ ≤ M * |dyadicCutoffMass| *
          (T ^ 2 * H ^ p * (Real.sqrt 2 * x ^ (-η / 4))) * H ^ s := by
        gcongr
      _ = M * T ^ 2 *
          (|dyadicCutoffMass| * Real.sqrt 2 * H ^ (p + s) * x ^ (-η / 4)) := by
        rw [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpayZero (by positivity)
  linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
