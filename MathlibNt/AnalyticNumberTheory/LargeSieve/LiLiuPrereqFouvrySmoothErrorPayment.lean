import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothErrorBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Paying the smooth errors at growing C.2 scales

The beta endpoint is at most `2 * x^(1/10)`, the modulus endpoint at most
`x^(5/9)`, and the alpha scale times the beta endpoint at most `x`.
The factor two includes the full dyadic beta interval at the endpoint
`N = x^(1/10)`, with the source normalization `x = 4 * M * N`.
The resulting polynomial exponent is `149/90 < 2`. These estimates concern
the actual U and V envelopes, not the remaining Kloosterman contribution.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset Filter
open scoped Topology

noncomputable section

/-- The exact polynomial slack used to pay both smooth errors. -/
theorem smooth_error_scale_product_le {x M T L : ℝ}
    (hx : 0 < x) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hMT : M * T ≤ x) (hTx : T ≤ 2 * x ^ (1 / 10 : ℝ))
    (hLx : L ≤ x ^ (5 / 9 : ℝ)) :
    M * T ^ 2 * L ≤ 2 * x ^ (149 / 90 : ℝ) := by
  calc
    _ = (M * T) * T * L := by ring
    _ ≤ x * (2 * x ^ (1 / 10 : ℝ)) * x ^ (5 / 9 : ℝ) := by gcongr
    _ = 2 * (x ^ (1 : ℝ) * x ^ (1 / 10 : ℝ) * x ^ (5 / 9 : ℝ)) := by
      rw [Real.rpow_one]
      ring
    _ = 2 * x ^ (149 / 90 : ℝ) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      norm_num

/-- Simultaneous payment of the actual two envelopes after the unrestricted
fixed-order alpha second moment. All three orders and the residue are retained. -/
theorem alpha_sq_mul_smooth_envelopes_le_c2
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j)
    {x M T L : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hMT : M * T ≤ x) (hTx : T ≤ 2 * x ^ (1 / 10 : ℝ))
    (hLx : L ≤ x ^ (5 / 9 : ℝ))
    (S N Q : Finset ℕ) (hS : ∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    (∑ m ∈ S, α m ^ 2) *
        (smoothUErrorEnvelope N Q β c a + smoothVErrorEnvelope N Q β c a) ≤
      8 * x ^ (149 / 90 : ℝ) *
        (1 + Real.log (2 * x)) ^ (i ^ 2 - 1 + 2 * (k - 1) + 8 * j) := by
  let H := 1 + Real.log (2 * x)
  have hH : 1 ≤ H := by
    have := Real.log_nonneg (show 1 ≤ 2 * x by linarith)
    dsimp [H]
    linarith
  have hMx : M ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ M) hT).trans hMT
  have hT' : T ≤ 2 * x := hTx.trans (by
    gcongr
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show (1 / 10 : ℝ) ≤ 1 by norm_num))
  have hL' : L ≤ x := hLx.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have log_mono : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * x → 1 + Real.log y ≤ H := by
    intro y hy hyx
    dsimp [H]
    gcongr
  have hlogT := Real.log_nonneg hT
  have hlogL := Real.log_nonneg hL
  have hpowT : (1 + Real.log T) ^ (k - 1) ≤ H ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) (log_mono T hT (by linarith)) _
  have hpowL : (1 + Real.log L) ^ (8 * j) ≤ H ^ (8 * j) :=
    pow_le_pow_left₀ (by positivity) (log_mono L hL (by linarith)) _
  have hpowL' : (1 + Real.log L) ^ (5 * j - 1) ≤ H ^ (8 * j) :=
    (pow_le_pow_left₀ (by positivity) (log_mono L hL (by linarith)) _).trans
      (pow_le_pow_right₀ hH (by omega))
  have hU : smoothUErrorEnvelope N Q β c a ≤
      T ^ 2 * L * H ^ (2 * (k - 1) + 8 * j) := by
    calc
      _ ≤ (T * (1 + Real.log T) ^ (k - 1)) ^ 2 * (1 + Real.log L) ^ (8 * j) :=
        smoothUErrorEnvelope_le_fouvryTau hk j hT hL N Q hN hQ β c hβ hc a
      _ ≤ (T * H ^ (k - 1)) ^ 2 * H ^ (8 * j) := by gcongr
      _ ≤ (T * H ^ (k - 1)) ^ 2 * H ^ (8 * j) * L :=
        le_mul_of_one_le_right (by positivity) hL
      _ = _ := by rw [pow_add, mul_pow, ← pow_mul]; ring
  have hV : smoothVErrorEnvelope N Q β c a ≤
      T ^ 2 * L * H ^ (2 * (k - 1) + 8 * j) := by
    calc
      _ ≤ (T * (1 + Real.log T) ^ (k - 1)) ^ 2 * L *
          (1 + Real.log L) ^ (5 * j - 1) :=
        smoothVErrorEnvelope_le_fouvryTau hk hj hT hL N Q hN hQ β c hβ hc a
      _ ≤ (T * H ^ (k - 1)) ^ 2 * L * H ^ (8 * j) := by gcongr
      _ = _ := by rw [pow_add, mul_pow, ← pow_mul]; ring
  have hA : (∑ m ∈ S, α m ^ 2) ≤ 2 * M * H ^ (i ^ 2 - 1) := by
    refine (sum_alpha_sq_dyadic_le hi hM S hS α hα).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀
      (by have := Real.log_nonneg (show 1 ≤ 2 * M by linarith); positivity)
      (log_mono (2 * M) (by linarith) (by linarith)) _
  calc
    _ ≤ (2 * M * H ^ (i ^ 2 - 1)) *
        (2 * (T ^ 2 * L * H ^ (2 * (k - 1) + 8 * j))) :=
      mul_le_mul hA (by linarith)
        (add_nonneg (smoothUErrorEnvelope_nonneg ..) (smoothVErrorEnvelope_nonneg ..))
        (by positivity)
    _ = 4 * (M * T ^ 2 * L) * H ^ (i ^ 2 - 1 + 2 * (k - 1) + 8 * j) := by
      simp only [pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      convert mul_le_mul_of_nonneg_left
        (smooth_error_scale_product_le (by linarith)
          (by linarith) (by linarith) hMT hTx hLx) (by norm_num : (0 : ℝ) ≤ 4) using 1
      ring

/-- Every fixed logarithm loss is absorbed by the explicit `31/90`
polynomial slack. The constant may depend on the fixed orders, not on `x`. -/
theorem eventually_smooth_error_log_payment (K A : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ (149 / 90 : ℝ) * (1 + Real.log (2 * x)) ^ K ≤
        x ^ 2 / Real.log x ^ A := by
  have hsmall : (fun x : ℝ => Real.log x ^ (K + A)) =o[atTop]
      (fun x => x ^ (31 / 90 : ℝ)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (K + A : ℕ) (by norm_num : (0 : ℝ) < 31 / 90)
  have hbound := (hsmall.const_mul_left (C * 3 ^ K)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hb hx hlog
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  have hH0 : 0 ≤ 1 + Real.log (2 * x) := by
    have := Real.log_nonneg (show 1 ≤ 2 * x by linarith)
    linarith
  have hH : 1 + Real.log (2 * x) ≤ 3 * Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hb' : C * 3 ^ K * Real.log x ^ (K + A) ≤ x ^ (31 / 90 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * 3 ^ K *
      Real.log x ^ (K + A)), abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hb
  apply (le_div_iff₀ (pow_pos hlog0 A)).mpr
  calc
    _ ≤ C * x ^ (149 / 90 : ℝ) * (3 * Real.log x) ^ K * Real.log x ^ A := by
      gcongr
    _ = x ^ (149 / 90 : ℝ) * (C * 3 ^ K * Real.log x ^ (K + A)) := by
      rw [pow_add, mul_pow]
      ring
    _ ≤ x ^ (149 / 90 : ℝ) * x ^ (31 / 90 : ℝ) :=
      mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hx0.le _)
    _ = x ^ 2 := by
      rw [← Real.rpow_add hx0]
      norm_num

/-- Uniform logarithmic payment after alpha L2 on the growing C.2 domains.
The threshold is chosen before every scale, support, signed coefficient, and
integer residue. In particular, `a` may vary freely with `x`. -/
theorem alpha_sq_mul_smooth_envelopes_c2_log_payment
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j)
    (A : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → M * T ≤ x →
      T ≤ 2 * x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      C * ((∑ m ∈ S, α m ^ 2) *
        (smoothUErrorEnvelope N Q β c a + smoothVErrorEnvelope N Q β c a)) ≤
          x ^ 2 / Real.log x ^ A := by
  filter_upwards [eventually_smooth_error_log_payment
    (i ^ 2 - 1 + 2 * (k - 1) + 8 * j) A (mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 8)),
    eventually_ge_atTop (1 : ℝ)] with x hp hx
  intro M T L hM hT hL hMT hTx hLx S N Q hS hN hQ α β c hα hβ hc a
  have h := mul_le_mul_of_nonneg_left
    (alpha_sq_mul_smooth_envelopes_le_c2 hi hk hj hx hM hT hL hMT hTx hLx
      S N Q hS hN hQ α β c hα hβ hc a) hC
  exact h.trans (by simpa only [mul_assoc] using hp)

/-- The actual signed U and V remainders, with the dispersion coefficient
`2` on V, are paid without any assumed error bound. The alpha support and the
larger finite cutoff support are separate, so smoothing introduces no false
support restriction. This does not estimate the W/Kloosterman term. -/
theorem dispersionUV_smooth_c2_log_payment
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j) (A : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → M * T ≤ x →
      T ≤ 2 * x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S P N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ P) →
      N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      (∑ m ∈ S, α m ^ 2) *
        (|dispersionU P N Q (fun m => scaledDyadicCutoff M m) β c a -
            smoothUMain M N Q β c a| +
          2 * |dispersionV P N Q (fun m => scaledDyadicCutoff M m) β c a -
            smoothUMain M N Q β c a|) ≤ x ^ 2 / Real.log x ^ A := by
  obtain ⟨CU, hCU, hU⟩ := dispersionU_smooth_uniform_error
  obtain ⟨CV, hCV, hV⟩ := dispersionV_smooth_uniform_error
  have hC : 0 ≤ CU + 2 * CV := by positivity
  filter_upwards [alpha_sq_mul_smooth_envelopes_c2_log_payment hi hk hj A hC] with x hx
  intro M T L hM hT hL hMT hTx hLx S P N Q hS hP hN hQ α β c hα hβ hc a
  have hQ0 : ∀ q ∈ Q, q ≠ 0 := fun q hq => (mem_Ioc.mp (hQ hq)).1.ne'
  have hu := hU M (by linarith) P hP N Q β c a hQ0
  have hv := hV M (by linarith) P hP N Q β c a hQ0
  have heu := smoothUErrorEnvelope_nonneg N Q β c a
  have hev := smoothVErrorEnvelope_nonneg N Q β c a
  calc
    _ ≤ (∑ m ∈ S, α m ^ 2) *
        ((CU + 2 * CV) * (smoothUErrorEnvelope N Q β c a + smoothVErrorEnvelope N Q β c a)) := by
      apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun _ _ => sq_nonneg _))
      nlinarith [mul_nonneg hCU.le hev, mul_nonneg hCV.le heu]
    _ = (CU + 2 * CV) * ((∑ m ∈ S, α m ^ 2) *
        (smoothUErrorEnvelope N Q β c a + smoothVErrorEnvelope N Q β c a)) := by ring
    _ ≤ _ := hx M T L hM hT hL hMT hTx hLx S N Q hS hN hQ α β c hα hβ hc a

/-- The original two dyadic intervals with `x = 4 M N`, including the
closed short-variable endpoint `N = x^(1/10)`. -/
theorem dispersionUV_smooth_c2_dyadic_log_payment
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j) (A : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x →
      T ≤ x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S P N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ P) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      (∑ m ∈ S, α m ^ 2) *
        (|dispersionU P N Q (fun m => scaledDyadicCutoff M m) β c a -
            smoothUMain M N Q β c a| +
          2 * |dispersionV P N Q (fun m => scaledDyadicCutoff M m) β c a -
            smoothUMain M N Q β c a|) ≤ x ^ 2 / Real.log x ^ A := by
  filter_upwards [dispersionUV_smooth_c2_log_payment hi hk hj A] with x hx
  intro M T L hM hT hL hxMT hTx hLx S P N Q hS hP hN hQ α β c hα hβ hc a
  have hN' : N ⊆ Ioc 0 ⌊2 * T⌋₊ := by
    intro n hn
    have hn' := hN n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor hn'.2⟩
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  exact hx M (2 * T) L hM (by linarith) hL
    (by nlinarith [mul_nonneg (by linarith : 0 ≤ M) (by linarith : 0 ≤ T)])
    (by linarith) hLx S P N Q hS hP hN' hQ α β c hα hβ hc a

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
