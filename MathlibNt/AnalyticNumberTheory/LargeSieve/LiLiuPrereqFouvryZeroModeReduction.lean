import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModePayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothErrorPayment

/-!
# The actual signed distribution error after zero-mode payment

At the source normalization `x = 4 M T`, the full zero-mode difference
and both U/V errors are paid. Only the original signed nonzero W mode is
retained. This is a reduction, not a bound for that oscillatory remainder.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset Filter
open scoped Topology

noncomputable section

/-- Uniform reduction of the actual signed bilinear distribution error at
the full dyadic C.2 scales. The given SW family is at the lower beta scale;
its doubled-scale transport is proved, not assumed. The W term stays signed. -/
theorem signedError_sq_le_nonzeroMode_c2
    {ι : Type*} {κ k ℓ j : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hj : 1 ≤ j) (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ i, 1 ≤ T i)
    (hN : ∀ i, ∀ n ∈ N i, T i ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T i)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T i = x →
      x ^ ε ≤ T i → T i ≤ x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau ℓ m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      signedError S (N i) Q α (β i) c a ^ 2 ≤
        (∑ m ∈ S, α m ^ 2) * smoothWNonzeroMode M (N i) Q (β i) c a +
          x ^ 2 / Real.log x ^ A := by
  have hN' : ∀ i, N i ⊆ Ioc 0 ⌊2 * T i⌋₊ := by
    intro i n hn
    have hn' := hN i n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor hn'.2⟩
    have : (0 : ℝ) < n := by linarith [hT i]
    exact_mod_cast this
  have hT' : ∀ i, 1 ≤ 2 * T i := fun i => by linarith [hT i]
  filter_upwards [
    alpha_sq_mul_smoothWU_SWFamily_log_payment hk hℓ j (A + 1)
      (hSW.double_scale hT) hT' hN' hβ hε,
    dispersionUV_smooth_c2_dyadic_log_payment hℓ hk hj (A + 1),
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hzero huv hx hxlog
  intro i M L hM hL hMT hεT hTx hLx S Q hS hQ α c hα hc a
  have hMpos : 0 < M := by linarith
  have hLx' : L ≤ x := hLx.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hzero' := hzero i M L hM hL
    (show M * (2 * T i) ≤ x by
      nlinarith [mul_nonneg hMpos.le (show 0 ≤ T i by linarith [hT i])])
    hLx' (show x ^ ε ≤ 2 * T i by linarith [hT i])
    S Q hS hQ α c hα hc a
  have huv' := huv M (T i) L hM (hT i) hL hMT hTx hLx
    S (dyadicCutoffNatSupport M) (N i) Q hS
    (scaledDyadicCutoff_mem_natSupport hMpos) (hN i) hQ α (β i) c hα (hβ i) hc a
  have hQ0 : ∀ q ∈ Q, q ≠ 0 := fun q hq => (mem_Ioc.mp (hQ hq)).1.ne'
  have hdisp := signedError_sq_le_dyadicCutoff_dispersion hMpos
    S (N i) Q α (β i) c a hS
  rw [dispersionW_eq_smoothWMain_add_nonzeroMode hMpos (N i) Q (β i) c a hQ0]
    at hdisp
  have hsum : 0 ≤ ∑ m ∈ S, α m ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have he : 2 * (x ^ 2 / Real.log x ^ (A + 1)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_succ (Real.log x) A, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < Real.log x)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (sub_nonneg.mpr hxlog)]
  have hmain := mul_le_mul_of_nonneg_left
    (le_abs_self (smoothWMain M (N i) Q (β i) c a -
      smoothUMain M (N i) Q (β i) c a)) hsum
  have hu := mul_le_mul_of_nonneg_left
    (le_abs_self (dispersionU (dyadicCutoffNatSupport M) (N i) Q
      (fun m => scaledDyadicCutoff M m) (β i) c a -
      smoothUMain M (N i) Q (β i) c a)) hsum
  have hv := mul_le_mul_of_nonneg_left
    (neg_le_abs (dispersionV (dyadicCutoffNatSupport M) (N i) Q
      (fun m => scaledDyadicCutoff M m) (β i) c a -
      smoothUMain M (N i) Q (β i) c a)) hsum
  nlinarith

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
