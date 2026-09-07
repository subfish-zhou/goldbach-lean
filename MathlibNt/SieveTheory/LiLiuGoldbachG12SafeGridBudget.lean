import MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetLogSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace G12SafeGridBudget

/-- A finite sum keeps the original main term and pays the fee once per cell. -/
theorem sum_cell_bounds {ι : Type*} (s : Finset ι) (output main : ι → ℝ)
    (fee : ℝ) (h : ∀ i ∈ s, output i ≤ main i + fee) :
    (∑ i ∈ s, output i) ≤ (∑ i ∈ s, main i) + s.card * fee := by
  calc
    _ ≤ ∑ i ∈ s, (main i + fee) := sum_le_sum h
    _ = _ := by simp [sum_add_distrib]

/-- Numerical outside budget, not a bound on the signed error beneath it. -/
theorem outside_numerical (B : ℕ) {η : ℝ} (hη : 0 < η) (hηu : η < 1/8) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℝ, (N : ℝ)^(1/3 : ℝ) ≤ Q → Q ≤ N →
      (20*N)*(4/(externalInternalLevel Q η)^(η^2))*(1+Real.log ⌊Q⌋₊)^2 ≤
        N / Real.log (N : ℝ)^B := by
  let c := (1/3 : ℝ)*((1+η+η^9)⁻¹*η^2)
  have hc0 : 0 < 1+η+η^9 := by positivity
  have hc : 0 < c := mul_pos (by norm_num) (mul_pos (inv_pos.mpr hc0) (sq_pos_of_pos hη))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (G12OutsideBudget.scalar_log_saving B hc)] with N hN
  intro Q hQl hQu
  have hN0 : (0 : ℝ) < N := by linarith [hN.1]
  have hQ1 : 1 ≤ Q := (Real.one_le_rpow (by linarith [hN.1] : (1 : ℝ) ≤ N)
    (by norm_num : (0 : ℝ) ≤ 1/3)).trans hQl
  have hf1 : (1 : ℝ) ≤ (⌊Q⌋₊ : ℕ) := by
    exact_mod_cast (Nat.le_floor (by simpa using hQ1) : 1 ≤ ⌊Q⌋₊)
  have hfN : (⌊Q⌋₊ : ℝ) ≤ N := (Nat.floor_le (by linarith : 0 ≤ Q)).trans hQu
  have hl := Real.log_le_log (by linarith : (0 : ℝ) < (⌊Q⌋₊ : ℕ)) hfN
  have hl0 := Real.log_nonneg hf1
  have hs : (1+Real.log (⌊Q⌋₊ : ℕ))^2 ≤ (1+Real.log (N : ℝ))^2 := by nlinarith
  have hd := G12OutsideBudget.denominator_lower hN0.le hη hηu hQl
  have hp : 0 < (N : ℝ)^c := Real.rpow_pos_of_pos hN0 c
  have hd0 : 0 ≤ (externalInternalLevel Q η)^(η^2) :=
    (hp.le.trans hd)
  have hb : 20*(4/(externalInternalLevel Q η)^(η^2))*(1+Real.log ⌊Q⌋₊)^2 ≤
      1/Real.log (N : ℝ)^B := by
    calc
      _ ≤ 20*(4/(externalInternalLevel Q η)^(η^2))*(1+Real.log (N : ℝ))^2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 20*(4/(N : ℝ)^c)*(1+Real.log (N : ℝ))^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) hp hd) (by norm_num)) (sq_nonneg _)
      _ = 80*(1+Real.log (N : ℝ))^2/(N : ℝ)^c := by ring
      _ ≤ _ := hN.2
  have hm := mul_le_mul_of_nonneg_left hb hN0.le
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hm

/-- Both displayed correction-budget summands are paid uniformly in the moving Q. -/
theorem correction_numerical (B : ℕ) {η : ℝ} (hη : 0 < η) (hηu : η < 1/8) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℝ, (N : ℝ)^(1/3 : ℝ) ≤ Q → Q ≤ N →
      G12FlexibleWF.correctionBudget N Q η ≤ 2*(N/Real.log (N : ℝ)^B) := by
  obtain ⟨J,_,hJ⟩ := G12RectangleGate.numerical_log_saving B
  filter_upwards [outside_numerical B hη hηu, eventually_ge_atTop J] with N ho hN
  intro Q hQl hQu
  have hg := hJ N hN
  rw [Real.rpow_natCast] at hg
  have hh := ho Q hQl hQu
  unfold G12FlexibleWF.correctionBudget
  linarith

end G12SafeGridBudget
