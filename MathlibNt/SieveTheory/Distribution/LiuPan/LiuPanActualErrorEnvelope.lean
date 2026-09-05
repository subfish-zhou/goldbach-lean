import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanConvolutionSourceCount
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanLiMainTermEnvelope

noncomputable section
open Finset
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiuWeight

def liuActualEnvelopeConstant (κ : ℝ) : ℝ :=
  6 + liuPanLiModulusEnvelopeConstant κ

theorem liuActualEnvelopeConstant_pos (κ : ℝ) : 0 < liuActualEnvelopeConstant κ := by
  have := liuPanLiModulusEnvelopeConstant_pos κ
  unfold liuActualEnvelopeConstant
  linarith

theorem liuCoprimeIntervalCount_nonneg (N z y A₁ A₂ q l : ℕ) :
    0 ≤ liuCoprimeIntervalCount N z y A₁ A₂ q l := by
  rw [liuCoprimeIntervalCount_eq_sum_betaInterval]
  exact sum_nonneg fun n _ => liuBetaInterval_nonneg N z y A₁ A₂ q n

theorem modulus_mul_liuCoprimeIntervalCount_le
    (N z y A₁ A₂ q l : ℕ) (hq : 0 < q) (hqN : q ≤ N) :
    (q : ℝ) * liuCoprimeIntervalCount N z y A₁ A₂ q l ≤ 6 * N := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  calc
    _ ≤ (q : ℝ) * (3 * ((N : ℝ) / q + 1)) :=
      mul_le_mul_of_nonneg_left
        (liuCoprimeIntervalCount_le_three_mul_real_div_add_one N z y A₁ A₂ q l hq) hqR.le
    _ = 3 * N + 3 * q := by field_simp
    _ ≤ _ := by linarith

/-- Literal whole-error envelope, uniform over every interval and residue. -/
theorem modulus_mul_abs_liuMainPanCoprimeIntervalSum_le (κ : ℝ)
    (N A₁ A₂ q l : ℕ) (hN : 2 ≤ N) (hq : 0 < q) (hqN : q ≤ N) :
    (q : ℝ) * |liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral κ)
      N A₁ A₂ q l (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
      liuActualEnvelopeConstant κ * N * (1 + Real.log N) ^ 2 := by
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hcount := modulus_mul_liuCoprimeIntervalCount_le
    N (liuSourceZ10 N) (liuSourceY3 N) A₁ A₂ q l hq hqN
  have hmain := modulus_mul_abs_liuPanLi_mainTerm_Ioc_le κ hN hq hqN A₁ A₂
  simp only [Finset.sum_filter, mul_div_assoc] at hmain
  rw [liuMainPanCoprimeIntervalSum_eq_count_sub_main]
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlog2 : 1 ≤ (1 + Real.log (N : ℝ)) ^ 2 := by nlinarith
  calc
    _ ≤ (q : ℝ) * (|liuCoprimeIntervalCount N (liuSourceZ10 N) (liuSourceY3 N) A₁ A₂ q l| +
      |∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          (liuLogarithmicIntegral κ ((N : ℝ) / a) / q.totient) else 0|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hqR
    _ ≤ 6 * N + liuPanLiModulusEnvelopeConstant κ * N * (1 + Real.log N) ^ 2 := by
      rw [mul_add, abs_of_nonneg (liuCoprimeIntervalCount_nonneg ..)]
      exact add_le_add hcount hmain
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ 6 * N by positivity)
      unfold liuActualEnvelopeConstant
      nlinarith

theorem liuMainPanCoprimeIntervalMaxL_nonneg
    (main : ℝ → ℝ) (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanCoprimeIntervalMaxL main N A₁ A₂ q f := by
  classical
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  split
  next h =>
    obtain ⟨l, hl⟩ := h
    apply (abs_nonneg (liuMainPanCoprimeIntervalSum main N A₁ A₂ q l f)).trans
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  next => exact le_rfl

/-- The actual reduced-residue maximum, including q=1, with a fixed κ constant. -/
theorem modulus_mul_liuMainPanCoprimeIntervalMaxL_le (κ : ℝ)
    (N A₁ A₂ q : ℕ) (hN : 2 ≤ N) (hq : 0 < q) (hqN : q ≤ N) :
    (q : ℝ) * liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ)
      N A₁ A₂ q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      liuActualEnvelopeConstant κ * N * (1 + Real.log N) ^ 2 := by
  classical
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  split
  next h =>
    apply (le_div_iff₀' (show (0 : ℝ) < q by exact_mod_cast hq)).mp
    apply Finset.max'_le
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    apply (le_div_iff₀' (show (0 : ℝ) < q by exact_mod_cast hq)).mpr
    exact modulus_mul_abs_liuMainPanCoprimeIntervalSum_le κ N A₁ A₂ q l hN hq hqN
  next =>
    simp only [mul_zero]
    exact mul_nonneg (mul_nonneg (liuActualEnvelopeConstant_pos κ).le (Nat.cast_nonneg _)) (sq_nonneg _)

end MathlibNt.SieveTheory.LiuWeight