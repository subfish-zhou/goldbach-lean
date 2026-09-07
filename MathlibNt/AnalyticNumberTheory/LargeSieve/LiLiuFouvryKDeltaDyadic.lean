import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDeltaPayment

/-!
# Large common-modulus payment at the C.2 dyadic scale

The actual beta endpoint is `2 * T` when `4 * M * T = x`. Both lengths have
a positive power lower bound with exponent `min ε (min η (1 / 2))`.
The original sum, zero mode and tail use one identical arbitrary mask.
The frequency cutoff is exactly `wUniformCutoff M (x ^ η)` throughout.
The fixed shift scale precedes the eventual threshold and all changing data.
The upper bound `T ≤ x^(1/9)` is used only to deduce `sqrt x ≤ M`
from the eventual inequality `4*x^(1/9+1/2) ≤ x`.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform logarithmic payment of every submask of the large common-modulus
part of the actual clean truncated W sum. No SW or nondivisibility assumption
on the original beta is required, and every divisor order may be zero. -/
theorem betaClean_wMaskedTruncated_largeDelta_dyadic_kscale
    (i k j A : ℕ) {ε η Cscale : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x →
      x ^ ε ≤ T → T ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
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
        x ^ η < (t.1.1.gcd t.1.2 : ℝ)) →
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q
          (betaClean β a) c a P| ≤ x ^ 2 / Real.log x ^ A := by
  let ρ : ℝ := min ε (min η (1 / 2))
  let u : ℕ := (i + 1) ^ 2 - 1
  have hρ : 0 < ρ := lt_min hε (lt_min hη (by norm_num))
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρη : ρ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hρhalf : ρ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [
    eventually_wMaskedOriginal_zero_largeDelta_power_saving_kscale
      (by omega : 1 ≤ k + 1) j hρ hρη hCscale,
    wMaskedTail_uniformCutoff_alpha_log_payment i k j (A + 1) hη,
    betaPayment_eventually_log_mul_rpow_le 4 (by norm_num) (u + (A + 1))
      (b := -ρ / 2) (d := 0) (by linarith),
    betaPayment_eventually_log_mul_rpow_le 4 (by norm_num) 0
      (b := (1 / 9 : ℝ) + 1 / 2) (d := 1) (by norm_num),
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with x hpower htail hpay hlong hx hlog
  intro M T L hM hT _hL hscale hlow hhigh hlevel S N Q hS hN hQ
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
  have hhalfM : x ^ (1 / 2 : ℝ) ≤ M := by
    have hbound : 4 * T * x ^ (1 / 2 : ℝ) ≤ 4 * T * M := by
      calc
        4 * T * x ^ (1 / 2 : ℝ) ≤
            4 * x ^ (1 / 9 : ℝ) * x ^ (1 / 2 : ℝ) := by gcongr
        _ = 4 * x ^ ((1 / 9 : ℝ) + 1 / 2) := by
          rw [mul_assoc, ← Real.rpow_add hx0]
        _ ≤ x := by simpa only [pow_zero, mul_one, Real.rpow_one] using hlong
        _ = 4 * T * M := by rw [← hscale]; ring
    exact le_of_mul_le_mul_left hbound (by positivity)
  have hρM : x ^ ρ ≤ M :=
    (Real.rpow_le_rpow_of_exponent_le hx hρhalf).trans hhalfM
  have hρT : x ^ ρ ≤ 2 * T :=
    ((Real.rpow_le_rpow_of_exponent_le hx hρε).trans hlow).trans (by linarith)
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
  have hheadPower := hpower M (2 * T) hM (by linarith) hMT hρM hρT
    N Q hNupper hQx (betaClean β a) c hclean' hc a hax
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
          (2 * M * (2 * T) ^ 2 * x ^ (-ρ / 2)) * H ^ (A + 1) := by
        apply mul_le_mul
          (mul_le_mul hAlpha hheadPower (by positivity) (by positivity))
          (pow_le_pow_left₀ hlog0.le (by dsimp [H]; linarith) _) (by positivity)
          (by positivity)
      _ = (M * (2 * T)) ^ 2 *
          (4 * H ^ (u + (A + 1)) * x ^ (-ρ / 2)) := by
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
