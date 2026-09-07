import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKLargeGCDOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWTailBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative first large-gcd exclusion for the actual nonzero W sum

The original progression sum, its zero mode and its Fourier tail are estimated
on the identical arbitrary mask supported on `gcd(n₁,n₂) > x^η`. This excludes
the first gcd coordinate, not the union of all five large-gcd coordinates.
The beta parameter `T` is an upper endpoint, not a dyadic lower endpoint.
The condition `β n ≠ 0 → n ∤ a` is retained; its preprocessing is separate.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All three already proved estimates on precisely the same mask. The
constants precede all scales, supports, coefficients, residue and mask. -/
theorem wMaskedTruncated_abs_le_largeGCD_kscale
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) (l : ℕ)
    {ε Cscale : ℝ} (hε : 0 < ε) (hCscale : 1 ≤ Cscale) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ M T L Y Z x : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 0 < Y → 0 < Z → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M Z) N Q β c a P| ≤
        C * M * x ^ ε *
          (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
            Real.sqrt ((1 + Real.log T) / Y)) +
        |M * dyadicCutoffMass| *
          (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
            Real.sqrt ((1 + Real.log T) / Y)) *
          (1 + Real.log L) ^ (2 * j ^ 2 + 1) +
        D * ((L * (1 + Real.log L) ^ (j - 1)) ^ 2 *
          (T * (1 + Real.log T) ^ (k - 1)) ^ 2) / Z ^ l := by
  obtain ⟨C, hC, hOriginal⟩ := wMaskedOriginal_abs_le_largeGCD_kscale hk j hε hCscale
  obtain ⟨D, hD, hTail⟩ := wMaskedTail_uniformCutoff_fouvryTau l
  refine ⟨C, D, hC, hD, ?_⟩
  intro M T L Y Z x hM hT hL hY hZ hx hMT N Q hN hQ β c hβ hc a ha hs P hP
  have hM0 : 0 < M := by linarith
  have he := wMaskedOriginal_eq_zero_add_truncated_add_tail hM0
    (wUniformCutoff M Z) N Q β c a P
    (fun q hq ↦ (mem_Ioc.mp (hQ hq)).1.ne')
  have ht : wMaskedTruncated M (wUniformCutoff M Z) N Q β c a P =
      (wMaskedOriginal M N Q β c a P - wMaskedZeroMode M N Q β c a P) -
        wMaskedTail M (wUniformCutoff M Z) N Q β c a P := by linarith
  rw [ht]
  calc
    _ ≤ |wMaskedOriginal M N Q β c a P - wMaskedZeroMode M N Q β c a P| +
        |wMaskedTail M (wUniformCutoff M Z) N Q β c a P| := abs_sub _ _
    _ ≤ |wMaskedOriginal M N Q β c a P| + |wMaskedZeroMode M N Q β c a P| +
        |wMaskedTail M (wUniformCutoff M Z) N Q β c a P| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ _ := add_le_add
      (add_le_add (hOriginal M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs P hP)
        (wMaskedZeroMode_abs_le_largeGCD hk j hT hL hY M N Q hN hQ β c hβ hc a P hP))
      (hTail M Z hM0 hZ k j hk hj T L hT hL N Q hN hQ β c hβ hc a P)

private theorem eventually_log_mul_rpow_le (K : ℝ) (hK : 0 ≤ K) (n : ℕ)
    {b d : ℝ} (hbd : b < d) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ n * x ^ b ≤ x ^ d := by
  have hb := ((isLittleO_log_rpow_rpow_atTop (n : ℝ)
    (sub_pos.mpr hbd)).const_mul_left (K * 2 ^ n)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hb' : K * 2 ^ n * Real.log x ^ n ≤ x ^ (d - b) := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ K * 2 ^ n * Real.log x ^ n),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hx
  calc
    _ ≤ K * (2 * Real.log x) ^ n * x ^ b := by
      gcongr
      linarith
    _ = (K * 2 ^ n * Real.log x ^ n) * x ^ b := by rw [mul_pow]; ring
    _ ≤ x ^ (d - b) * x ^ b :=
      mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hx0.le _)
    _ = x ^ d := by rw [← Real.rpow_add hx0]; congr 1; ring

private theorem sqrt_log_div_rpow_le {x T η : ℝ}
    (hx : 1 ≤ x) (hT : 1 ≤ T) (hTx : T ≤ x) :
    Real.sqrt ((1 + Real.log T) / x ^ η) ≤
      (1 + Real.log x) * x ^ (-η / 2) := by
  have hx0 : 0 < x := by linarith
  have hH : 1 ≤ 1 + Real.log x := by have := Real.log_nonneg hx; linarith
  have hHT : 1 + Real.log T ≤ 1 + Real.log x := by
    have := Real.log_le_log (by linarith : 0 < T) hTx
    linarith
  have hs : Real.sqrt (1 + Real.log T) ≤ 1 + Real.log x := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith, ?_⟩
    nlinarith
  have hp : Real.sqrt (x ^ η) = x ^ (η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [Real.sqrt_div (by have := Real.log_nonneg hT; positivity), hp]
  calc
    _ ≤ (1 + Real.log x) / x ^ (η / 2) :=
      div_le_div_of_nonneg_right hs (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le]; congr 2; ring

/-- A power saving for the actual finite nonzero-frequency sum. The cutoff is
constructed, the mask is arbitrary within the first large-beta-gcd exclusion,
and the eventual threshold depends only on the fixed orders, `η`, and `Cscale`. -/
theorem eventually_wMaskedTruncated_largeGCD_power_saving_kscale
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) {η Cscale : ℝ} (hη : 0 < η) (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
        3 * M * T ^ 2 * x ^ (-η / 8) := by
  obtain ⟨l, hl⟩ := exists_nat_gt ((2 + η) / η)
  have hl' : 2 + η < η * (l : ℝ) := by
    have := (div_lt_iff₀ hη).mp hl
    nlinarith
  obtain ⟨C, D, hC, hD, hb⟩ :=
    wMaskedTruncated_abs_le_largeGCD_kscale hk hj l (show 0 < η / 8 by linarith) hCscale
  let p := k ^ 2 - 1
  let s := 2 * j ^ 2 + 1
  let v := 2 * (j - 1) + 2 * (k - 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_log_mul_rpow_le C hC.le (p + 1)
      (show η / 8 - η / 2 < -η / 8 by linarith),
    eventually_log_mul_rpow_le |dyadicCutoffMass| (abs_nonneg _) (p + 1 + s)
      (show -η / 2 < -η / 8 by linarith),
    eventually_log_mul_rpow_le D hD.le v
      (show 2 - η * (l : ℝ) < -η / 8 by linarith)] with x hx hOrig hZero hTail
  intro M T hM hT hMT N Q hN hQ β c hβ hc a ha hs P hP
  have hx0 : 0 < x := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTx : T ≤ x := (le_mul_of_one_le_left hT0 hM).trans hMT
  have hlogT := Real.log_nonneg hT
  have hlogx := Real.log_nonneg hx
  let H := 1 + Real.log x
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHT : 1 + Real.log T ≤ H := by
    have := Real.log_le_log (by linarith : 0 < T) hTx
    dsimp [H]
    linarith
  have hSqrt := sqrt_log_div_rpow_le (η := η) hx hT hTx
  have hOrig' : C * M * x ^ (η / 8) *
      (T ^ 2 * (1 + Real.log T) ^ p * Real.sqrt ((1 + Real.log T) / x ^ η)) ≤
        M * T ^ 2 * x ^ (-η / 8) := by
    calc
      _ ≤ C * M * x ^ (η / 8) * (T ^ 2 * H ^ p * (H * x ^ (-η / 2))) := by
        gcongr
      _ = M * T ^ 2 * (C * H ^ (p + 1) * x ^ (η / 8 - η / 2)) := by
        rw [Real.rpow_sub hx0, show -η / 2 = -(η / 2) by ring, Real.rpow_neg hx0.le]
        simp only [pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hOrig (by positivity)
  have hZero' : |M * dyadicCutoffMass| *
      (T ^ 2 * (1 + Real.log T) ^ p * Real.sqrt ((1 + Real.log T) / x ^ η)) *
        H ^ s ≤ M * T ^ 2 * x ^ (-η / 8) := by
    rw [abs_mul, abs_of_nonneg hM0]
    calc
      _ ≤ M * |dyadicCutoffMass| *
          (T ^ 2 * H ^ p * (H * x ^ (-η / 2))) * H ^ s := by gcongr
      _ = M * T ^ 2 * (|dyadicCutoffMass| * H ^ (p + 1 + s) * x ^ (-η / 2)) := by
        simp only [pow_add, pow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZero (by positivity)
  have hTail' : D * ((x * H ^ (j - 1)) ^ 2 *
      (T * (1 + Real.log T) ^ (k - 1)) ^ 2) / (x ^ η) ^ l ≤
        M * T ^ 2 * x ^ (-η / 8) := by
    calc
      _ ≤ D * ((x * H ^ (j - 1)) ^ 2 * (T * H ^ (k - 1)) ^ 2) /
          (x ^ η) ^ l := by gcongr
      _ = T ^ 2 * (D * H ^ v * x ^ (2 - η * (l : ℝ))) := by
        rw [Real.rpow_sub hx0, Real.rpow_mul_natCast hx0.le, Real.rpow_two]
        have hv : v = (j - 1) * 2 + (k - 1) * 2 := by dsimp [v]; omega
        rw [hv]
        simp only [pow_add, pow_mul, mul_pow]
        ring
      _ ≤ T ^ 2 * x ^ (-η / 8) :=
        mul_le_mul_of_nonneg_left hTail (sq_nonneg _)
      _ ≤ _ := by
        simpa only [one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hM
            (show 0 ≤ T ^ 2 * x ^ (-η / 8) by positivity)
  have h := hb M T x (x ^ η) (x ^ η) x hM hT hx
    (Real.rpow_pos_of_pos hx0 _) (Real.rpow_pos_of_pos hx0 _) hx hMT
    N Q hN hQ β c hβ hc a ha hs P hP
  calc
    _ ≤ _ := h
    _ ≤ 3 * M * T ^ 2 * x ^ (-η / 8) := by
      dsimp [p, s, H] at hOrig' hZero' hTail'
      linarith

/-- Explicit uniform threshold version of the power saving. -/
theorem wMaskedTruncated_largeGCD_power_saving_kscale
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) {η Cscale : ℝ} (hη : 0 < η) (hCscale : 1 ≤ Cscale) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
        3 * M * T ^ 2 * x ^ (-η / 8) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (eventually_wMaskedTruncated_largeGCD_power_saving_kscale hk hj hη hCscale)
  exact ⟨max 1 x₀, le_max_left _ _, fun x hx ↦ hx₀ x ((le_max_right _ _).trans hx)⟩

/-- The actual alpha square sum pays every fixed natural logarithmic loss.
The threshold is uniform in both scales, all three signed coefficients,
supports, the varying residue and every submask of the first gcd exclusion. -/
theorem wMaskedTruncated_largeGCD_alpha_log_payment_kscale
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j)
    (A : ℕ) {η Cscale : ℝ} (hη : 0 < η) (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
          x ^ 2 / Real.log x ^ A := by
  let u := i ^ 2 - 1
  let K : ℝ := 6 * 2 ^ u
  filter_upwards [eventually_wMaskedTruncated_largeGCD_power_saving_kscale hk hj hη hCscale,
    eventually_log_mul_rpow_le K (by dsimp [K]; positivity) (u + A)
      (show -η / 8 < 0 by linarith),
    eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hW hb hx hlog
  intro M T hM hT hMT S N Q hS hN hQ α β c hα hβ hc a ha hs P hP
  have hx0 : 0 < x := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  have hMx : M ≤ x := (le_mul_of_one_le_right hM0 hT).trans hMT
  let H := 1 + Real.log x
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHM : 1 + Real.log (2 * M) ≤ 2 * H := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : M ≠ 0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_le_log (by linarith : 0 < M) hMx
    dsimp [H]
    linarith
  have hAlpha : (∑ m ∈ S, α m ^ 2) ≤ 2 * M * (2 * H) ^ u := by
    apply (sum_alpha_sq_dyadic_le hi hM S hS α hα).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀
      (by have := Real.log_nonneg (show 1 ≤ 2 * M by linarith); positivity) hHM _
  have hTrunc := hW M T hM hT hMT N Q hN hQ β c hβ hc a ha hs P hP
  have hb' : K * H ^ (u + A) * x ^ (-η / 8) ≤ 1 := by
    simpa only [Real.rpow_zero] using hb
  have hlogH : Real.log x ^ A ≤ H ^ A :=
    pow_le_pow_left₀ hlog0.le (by dsimp [H]; linarith) _
  apply (le_div_iff₀ (pow_pos hlog0 A)).mpr
  calc
    _ ≤ (2 * M * (2 * H) ^ u) *
        (3 * M * T ^ 2 * x ^ (-η / 8)) * H ^ A := by
      exact mul_le_mul (mul_le_mul hAlpha hTrunc (abs_nonneg _) (by positivity))
        hlogH (by positivity) (by positivity)
    _ = (M * T) ^ 2 * (K * H ^ (u + A) * x ^ (-η / 8)) := by
      dsimp [K]
      simp only [mul_pow, pow_add]
      ring
    _ ≤ x ^ 2 * 1 :=
      mul_le_mul (pow_le_pow_left₀ (mul_nonneg hM0 hT0) hMT 2) hb'
        (by positivity) (sq_nonneg _)
    _ = _ := mul_one _

/-- Real logarithmic exponents are paid as well, by rounding the requested
loss upward. No restriction on the fixed real exponent is needed. -/
theorem wMaskedTruncated_largeGCD_alpha_real_log_payment_kscale
    {i k j : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) (hj : 1 ≤ j)
    (A : ℝ) {η Cscale : ℝ} (hη : 0 < η) (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℝ,
      1 ≤ M → 1 ≤ T → M * T ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P| ≤
          x ^ 2 / (Real.log x) ^ A := by
  filter_upwards [wMaskedTruncated_largeGCD_alpha_log_payment_kscale hi hk hj ⌈A⌉₊ hη hCscale,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hp hlog
  intro M T hM hT hMT S N Q hS hN hQ α β c hα hβ hc a ha hs P hP
  apply (hp M T hM hT hMT S N Q hS hN hQ α β c hα hβ hc a ha hs P hP).trans
  apply div_le_div_of_nonneg_left (sq_nonneg x)
    (Real.rpow_pos_of_pos (by linarith : 0 < Real.log x) A)
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le hlog (Nat.le_ceil A)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

