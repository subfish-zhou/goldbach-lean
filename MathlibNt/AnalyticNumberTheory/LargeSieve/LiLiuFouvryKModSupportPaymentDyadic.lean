import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKModSupportPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKModSupportGeometry

/-!
# Supported-modulus exclusions at the actual C.2 scale

For `x = 4MT`, `T ≤ x^(1/9)` and `L ≤ x^(5/9)` imply `L ≤ M`
eventually. This pays the actual progression endpoints and preserves the same
mask in the original sum, exact zero mode, and uniformly truncated tail.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Both supported modulus factors are paid together, even inside an arbitrary
further submask. All fixed orders may be zero; no SW or nondivisibility premise
is imposed on the original beta coefficients. -/
theorem betaClean_wMaskedTruncated_modulus_support_dyadic_kscale
    (Cscale : ℝ) (hCscale : 1 ≤ Cscale)
    (i k j A : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x →
      T ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t →
        x ^ η < ((wGCDTuple t).δ₁ : ℝ) ∨ x ^ η < ((wGCDTuple t).δ₂ : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q
          (betaClean β a) c a P| ≤ x ^ 2 / Real.log x ^ A := by
  let u : ℕ := (i + 1) ^ 2 - 1
  filter_upwards [
    eventually_wMaskedOriginal_zero_modulus_support_power_saving_kscale Cscale hCscale
      (by omega : 1 ≤ k + 1) j hη,
    wMaskedTail_uniformCutoff_alpha_log_payment i k j (A + 1) hη,
    betaPayment_eventually_log_mul_rpow_le 4 (by norm_num) (u + (A + 1))
      (b := -η / 4) (d := 0) (by linarith),
    kModSupport_eventually_level_le_long,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with x hpower htail hpay hlong hx hlog
  intro M T L hM hT hL hscale hhigh hlevel S N Q hS hN hQ
    α β c hα hβ hc a hax P hP
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hT0 : 0 < T := by linarith
  have hMT : M * (2 * T) ≤ x := by nlinarith
  have hMx : 2 * M ≤ x := by nlinarith
  have hTx : 2 * T ≤ x := by nlinarith
  have hLx : L ≤ x := hlevel.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hLM : L ≤ M := hlong M T L hT0 hscale hhigh hlevel
  have hNupper : N ⊆ Ioc 0 ⌊2 * T⌋₊ := by
    intro n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hN n hn).2⟩
    have : (0 : ℝ) < n := by have := (hN n hn).1; linarith
    exact_mod_cast this
  have hSx : S ⊆ Ioc 0 ⌊x⌋₊ := by
    intro m hm
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor ((hS m hm).2.trans hMx)⟩
    have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
    exact_mod_cast this
  have hNx : N ⊆ Ioc 0 ⌊x⌋₊ :=
    hNupper.trans (Ioc_subset_Ioc_right (Nat.floor_mono hTx))
  have hQx : Q ⊆ Ioc 0 ⌊x⌋₊ :=
    hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hLx))
  have hclean : ∀ n ∈ N, |betaClean β a n| ≤ (fouvryTau k n : ℝ) :=
    fun n hn ↦ (abs_betaClean_le _ _ _).trans (hβ n hn)
  have hclean' : ∀ n ∈ N, |betaClean β a n| ≤ (fouvryTau (k + 1) n : ℝ) :=
    fun n hn ↦ (hclean n hn).trans (by exact_mod_cast fouvryTau_le_succ k n)
  have hα' : ∀ m ∈ S, |α m| ≤ (fouvryTau (i + 1) m : ℝ) :=
    fun m hm ↦ (hα m hm).trans (by exact_mod_cast fouvryTau_le_succ i m)
  have hheadPower := hpower M (2 * T) L hM (by linarith) hL hMT hLM
    N Q hNupper hQ (betaClean β a) c hclean' hc a hax
    (fun _ _ hn ↦ betaClean_nonzero_not_dvd hn) P hP
  have htailPay := htail M hM0 S N Q hSx hNx hQx α (betaClean β a) c
    hα hclean hc a P
  let H := 1 + Real.log x
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hlog0 : 0 < Real.log x := by linarith
  have hAlpha : (∑ m ∈ S, α m ^ 2) ≤ 2 * M * H ^ u := by
    apply (sum_alpha_sq_dyadic_le (by omega : 1 ≤ i + 1) hM S hS α hα').trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1 ≤ 2 * M by linarith)])
    dsimp [H]
    linarith [Real.log_le_log (by positivity : 0 < 2 * M) hMx]
  have hheadPay :
      (∑ m ∈ S, α m ^ 2) *
          (|wMaskedOriginal M N Q (betaClean β a) c a P| +
            |wMaskedZeroMode M N Q (betaClean β a) c a P|) ≤
        x ^ 2 / Real.log x ^ (A + 1) := by
    apply (le_div_iff₀ (pow_pos hlog0 (A + 1))).mpr
    calc
      _ ≤ (2 * M * H ^ u) *
          (2 * M * (2 * T) ^ 2 * x ^ (-η / 4)) * H ^ (A + 1) := by
        apply mul_le_mul
          (mul_le_mul hAlpha hheadPower (by positivity) (by positivity))
          (pow_le_pow_left₀ hlog0.le (by dsimp [H]; linarith) _) (by positivity)
          (by positivity)
      _ = (M * (2 * T)) ^ 2 *
          (4 * H ^ (u + (A + 1)) * x ^ (-η / 4)) := by
        rw [pow_add]
        ring
      _ ≤ x ^ 2 * 1 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hMT 2)
          (by simpa only [Real.rpow_zero] using hpay) (by positivity) (sq_nonneg _)
      _ = _ := mul_one _
  have he := wMaskedOriginal_eq_zero_add_truncated_add_tail hM0
    (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P
    (fun q hq ↦ (mem_Ioc.mp (hQx hq)).1.ne')
  have htrunc :
      wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P =
        (wMaskedOriginal M N Q (betaClean β a) c a P -
          wMaskedZeroMode M N Q (betaClean β a) c a P) -
            wMaskedTail M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P := by
    linarith
  have htri :
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P| ≤
        |wMaskedOriginal M N Q (betaClean β a) c a P| +
          |wMaskedZeroMode M N Q (betaClean β a) c a P| +
            |wMaskedTail M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P| := by
    rw [htrunc]
    exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  have hα0 : 0 ≤ ∑ m ∈ S, α m ^ 2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have htwo : 2 * (x ^ 2 / Real.log x ^ (A + 1)) ≤
      x ^ 2 / Real.log x ^ A := by
    rw [pow_succ (Real.log x) A, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ hlog0).mpr
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
  calc
    _ ≤ (∑ m ∈ S, α m ^ 2) *
        (|wMaskedOriginal M N Q (betaClean β a) c a P| +
          |wMaskedZeroMode M N Q (betaClean β a) c a P| +
            |wMaskedTail M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P|) :=
      mul_le_mul_of_nonneg_left htri hα0
    _ ≤ 2 * (x ^ 2 / Real.log x ^ (A + 1)) := by
      rw [mul_add]
      linarith
    _ ≤ _ := htwo

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
