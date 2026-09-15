import OriginalBoundaryEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8.Weighted
theorem low_nonneg {a : ℝ} (ha : 1/20 ≤ a) (hab : a ≤ 1/10) : 0 ≤ low a := by
  rw [low_eq_setIntegral ha hab]
  apply setIntegral_nonneg measurableSet_source
  intro x hx
  exact (fouvryG9WeightedIntegrand_bounds (source_subset_ambient ha hx)).1

/-- Fixed delta and rho precede N. The whole original domain, not an interior
rectangle, occurs on the right. -/
theorem original_kernel_fixed (ρ δ ε : ℝ) (hρ : 1 < ρ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      relaxedPairKernel N ρ δ ≤ (1+6*δ)*((9/5 : ℝ)*low (100/1327))+ε := by
  have ht : 0 < ε/(2*(1+6*δ)) := by positivity
  obtain ⟨n, hn, h, hh, hhs, hU⟩ := exists_upperSum_le_low_add
    (a := (100/1327 : ℝ)) (by norm_num) (by norm_num) _ ht
  obtain ⟨N₀, _, hN₀⟩ := original_kernel_le_upperSum_eventually n hn ρ h δ (ε/2)
    hρ hh hhs (by linarith) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hpert := upperSum_delta hn h hδ0 hδ
  have hmul := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 1+6*δ)
  have heq : (1+6*δ)*(ε/(2*(1+6*δ))) = ε/2 := by
    have hd : 1+6*δ ≠ 0 := by positivity
    field_simp
  have hmain := hN₀ N hN
  nlinarith

theorem original_kernel_final (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1/4 ∧
      ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ρ₀ ≤ 5/4 ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
          ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ₀ →
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
              ρ^3 * relaxedPairKernel N ρ δ ≤
                (9/5 : ℝ)*low (100/1327) + τ := by
  let B : ℝ := (9/5 : ℝ)*low (100/1327)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (low_nonneg (by norm_num) (by norm_num))
  let s : ℝ := min (1/4) (τ/(100*(B+1)))
  have hs : 0 < s := lt_min (by norm_num) (div_pos hτ (by positivity))
  have hsquarter : s ≤ 1/4 := min_le_left _ _
  have hs1 : s ≤ 1 := by linarith
  have hpay : 6*s*(B+1) ≤ τ := by
    have he := (le_div_iff₀ (show 0 < 100*(B+1) by positivity)).mp
      (min_le_right (1/4 : ℝ) (τ/(100*(B+1))))
    change s*(100*(B+1)) ≤ τ at he
    nlinarith [mul_nonneg hs.le (show 0 ≤ B+1 by positivity)]
  obtain ⟨n, hn, h, hh, hhsmall, hU⟩ :=
    exists_upperSum_le_low_add (a := (100/1327 : ℝ)) (by norm_num) (by norm_num) s hs
  change upperSum (100/1327) n h 0 ≤ B+s at hU
  refine ⟨s/6, by positivity, by linarith, 1+s/10, by linarith, by linarith, ?_⟩
  intro δ hδ0 hδ ρ hρ hρu
  have hδsmall : δ ≤ 1/8 := by linarith
  have hd : 1+6*δ ≤ 1+s := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hcube : ρ^3 ≤ 1+s := by
    have hc := fouvryG9MainScalar_cube
      (show 0 ≤ s/10 by positivity) (show s/10 ≤ 1 by linarith)
    have hm : ρ^3 ≤ (1+s/10)^3 := pow_le_pow_left₀ hρ0 hρu 3
    linarith
  have hUδ : upperSum (100/1327) n h δ ≤ (1+s)*(B+s) := by
    calc
      _ ≤ (1+6*δ)*upperSum (100/1327) n h 0 :=
        upperSum_delta hn h hδ0 hδsmall
      _ ≤ (1+6*δ)*(B+s) := mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ (1+s)*(B+s) := mul_le_mul_of_nonneg_right hd (by positivity)
  obtain ⟨N₀, _, hN₀⟩ := original_kernel_le_upperSum_eventually
    n hn ρ h δ s hρ hh hhsmall (by linarith) hs
  refine ⟨N₀, ?_⟩
  intro N hN
  have hK : relaxedPairKernel N ρ δ ≤ (1+s)*(B+s)+s :=
    (hN₀ N hN).trans (by linarith)
  have hs2 : s^2 ≤ s := by nlinarith
  have hinner : (1+s)*(B+s)+s ≤ (1+s)*B+3*s := by nlinarith
  have hBs2 : s^2*B ≤ s*B := mul_le_mul_of_nonneg_right hs2 hB
  have hbudget : (1+s)*((1+s)*(B+s)+s) ≤ B+6*s*(B+1) := by
    have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 1+s by positivity)
    nlinarith [mul_nonneg hs.le hB]
  calc
    _ ≤ ρ^3*((1+s)*(B+s)+s) := mul_le_mul_of_nonneg_left hK (pow_nonneg hρ0 3)
    _ ≤ (1+s)*((1+s)*(B+s)+s) :=
      mul_le_mul_of_nonneg_right hcube (by positivity)
    _ ≤ B+6*s*(B+1) := hbudget
    _ ≤ B+τ := by linarith


end OriginalU8.Weighted
