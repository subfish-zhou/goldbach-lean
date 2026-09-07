import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryIntegral
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar

noncomputable section
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Positivity of the literal production integral, not an auxiliary integral hypothesis. -/
theorem fouvryG9KernelBudget_low_nonneg : 0 ≤ fouvryG9RelaxedIntegralLow := by
  rw [fouvryG9RelaxedIntegralLow_eq_single]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hlog : 0 ≤ Real.log (2-3*u) := Real.log_nonneg (by linarith [hu.2])
  exact div_nonneg hlog (mul_nonneg hu0 (sq_nonneg _))

/-- All perturbations, including the actual rho cube, are paid before the N threshold. -/
theorem fouvryG9RelaxedPairKernel_final (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1/4 ∧
      ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ρ₀ ≤ 5/4 ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
          ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ₀ →
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
              ρ^3 * fouvryG9RelaxedPairKernel N ρ δ ≤
                (9/5 : ℝ)*fouvryG9RelaxedIntegralLow + τ := by
  let B : ℝ := (9/5 : ℝ)*fouvryG9RelaxedIntegralLow
  have hB : 0 ≤ B := mul_nonneg (by norm_num) fouvryG9KernelBudget_low_nonneg
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
    exists_fouvryG9RelaxedIntegralUpperSum_le_low_add s hs
  change fouvryG9RelaxedIntegralUpperSum n h 0 ≤ B+s at hU
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
  have hUδ : fouvryG9RelaxedIntegralUpperSum n h δ ≤ (1+s)*(B+s) := by
    calc
      _ ≤ (1+6*δ)*fouvryG9RelaxedIntegralUpperSum n h 0 :=
        fouvryG9RelaxedIntegral_upperSum_delta hn h hδ0 hδsmall
      _ ≤ (1+6*δ)*(B+s) := mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ (1+s)*(B+s) := mul_le_mul_of_nonneg_right hd (by positivity)
  obtain ⟨N₀, _, hN₀⟩ := fouvryG9RelaxedIntegral_kernel_le_upperSum_eventually
    n hn ρ h δ s hρ hh hhsmall (by linarith) hs
  refine ⟨N₀, ?_⟩
  intro N hN
  have hK : fouvryG9RelaxedPairKernel N ρ δ ≤ (1+s)*(B+s)+s :=
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

#print axioms fouvryG9KernelBudget_low_nonneg
#print axioms fouvryG9RelaxedPairKernel_final

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
