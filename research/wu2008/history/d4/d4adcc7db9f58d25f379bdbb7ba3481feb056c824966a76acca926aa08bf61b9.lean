import MathlibNt.Wu2004MeanValue.EndpointConsumers
import MathlibNt.Wu2004MeanValue.SourceMasks

/-! Simultaneous real/natural scale transport. The extra logarithm in the
level pays for the ceiling and the fixed product-ratio constant. -/

namespace Wu2004MeanValue

noncomputable section

def commonScale (K x : ℝ) : ℕ := ⌈max 1 K * x⌉₊

theorem commonScale_bounds (K x : ℝ) (hx : 1 ≤ x) :
    x ≤ (commonScale K x : ℝ) ∧ K * x ≤ (commonScale K x : ℝ) ∧
      (commonScale K x : ℝ) ≤ (max 1 K + 1) * x := by
  have hx0 : 0 ≤ x := by linarith
  have hL : 1 ≤ max 1 K := le_max_left _ _
  have hN : max 1 K * x ≤ (commonScale K x : ℝ) := Nat.le_ceil _
  refine ⟨?_, (mul_le_mul_of_nonneg_right (le_max_right 1 K) hx0).trans hN, ?_⟩
  · have := mul_le_mul_of_nonneg_right hL hx0
    linarith
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ max 1 K * x by positivity)
    dsimp [commonScale]
    linarith

theorem commonScale_cutoff (K x B : ℝ) (hB : 0 ≤ B)
    (hx3 : 3 ≤ x) (hxK : max 1 K + 1 ≤ x)
    (hxexp : Real.exp ((2 : ℝ) ^ B) ≤ x) :
    Real.sqrt x / Real.log x ^ (B + 1) ≤
      Real.sqrt (commonScale K x) / Real.log (commonScale K x : ℝ) ^ B := by
  obtain ⟨hxN, _, hNupper⟩ := commonScale_bounds K x (by linarith)
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogB : (2 : ℝ) ^ B ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  have hNxx : (commonScale K x : ℝ) ≤ x ^ 2 := by nlinarith
  have hlogN : 0 < Real.log (commonScale K x : ℝ) := Real.log_pos (by linarith)
  have hloghi : Real.log (commonScale K x : ℝ) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hNxx
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : Real.log (commonScale K x : ℝ) ^ B ≤ Real.log x ^ (B + 1) := by
    calc
      _ ≤ (2 * Real.log x) ^ B := Real.rpow_le_rpow hlogN.le hloghi hB
      _ = (2 : ℝ) ^ B * Real.log x ^ B := Real.mul_rpow (by norm_num) hlog0.le
      _ ≤ Real.log x * Real.log x ^ B :=
        mul_le_mul_of_nonneg_right hlogB (Real.rpow_nonneg hlog0.le _)
      _ = _ := by rw [Real.rpow_add hlog0, Real.rpow_one]; ring
  exact div_le_div₀ (Real.sqrt_nonneg (commonScale K x : ℝ))
    (Real.sqrt_le_sqrt hxN) (Real.rpow_pos_of_pos hlogN B) hpow

theorem commonScale_log_saving (K x A C : ℝ) (hx : 1 < x)
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    C * (commonScale K x : ℝ) / Real.log (commonScale K x : ℝ) ^ A ≤
      (C * (max 1 K + 1)) * x / Real.log x ^ A := by
  obtain ⟨hxN, _, hNupper⟩ := commonScale_bounds K x hx.le
  have hlog0 := Real.log_pos hx
  have hlogs := Real.log_le_log (by linarith : 0 < x) hxN
  calc
    _ ≤ C * ((max 1 K + 1) * x) / Real.log x ^ A := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hNupper hC) (Real.rpow_pos_of_pos hlog0 A)
        (Real.rpow_le_rpow hlog0.le hlogs hA)
    _ = _ := by ring

theorem block_source_sqrt_domain (H N a η : ℝ) (m : ℕ)
    (hne : blockLower H m < blockUpper H N a η m) :
    (m : ℝ) ≤ Real.sqrt (2 * H) := by
  have hs : (m : ℝ) ^ 2 ≤ blockLower H m := le_max_right _ _
  have hu : blockUpper H N a η m ≤ 2 * H :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hsq := hs.trans (hne.le.trans hu)
  exact (Real.le_sqrt (Nat.cast_nonneg m) ((sq_nonneg _).trans hsq)).mpr hsq

end
end Wu2004MeanValue
