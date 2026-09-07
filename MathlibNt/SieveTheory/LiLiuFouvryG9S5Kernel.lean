import MathlibNt.SieveTheory.LiLiuFouvryG9NormalizedError
import MathlibNt.SieveTheory.LiLiuFouvryG9MassKernel
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegral

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Literal low S5 reaches the actual relaxed kernel with all previous losses paid. -/
theorem fouvryG9S5Low_kernel_upper (τ ξ ζ : ℝ)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hζ : 0 < ζ)
    {e ε δ ρ : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 4/53) (hεδ : ε < δ) (hδ : δ < 1/4)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N e) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^(1/10 : ℝ)) : ℝ) ≤
        (4*(1+τ)*(1+ξ)*(ρ^3*fouvryG9RelaxedPairKernel N ρ δ)+ζ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨Ns,hs⟩ := fouvryG9S5Low_weighted_mass_upper τ ζ hτ hζ
    he he1 hε hεa hεδ hδ hρ hρu
  obtain ⟨Nm,hm⟩ := fouvryG9RectangleMass_le_kernel he hρ hρu hδ hξ
  refine ⟨max Ns Nm,?_⟩
  intro N hN hEven
  have hsN := hs N ((le_max_left _ _).trans hN) hEven
  have hmN := hm N ((le_max_right _ _).trans hN)
  have hC : 0 ≤ 4*(1+τ)*SingularSeries.liuSingularSeries N := by
    have := (SingularSeries.liuSingularSeries_pos N).le
    positivity
  have h := add_le_add (mul_le_mul_of_nonneg_left hmN hC)
    (le_refl (ζ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2)))
  apply hsN.trans
  convert h using 1
  ring

/-- Positivity of the literal weighted low integral, using its proved single form. -/
theorem fouvryG9LowIntegral_nonneg : 0 ≤ fouvryG9RelaxedIntegralLow := by
  rw [fouvryG9RelaxedIntegralLow_eq_single]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  apply div_nonneg
  · apply Real.log_nonneg
    linarith [hu.2]
  · exact mul_nonneg (by linarith [hu.1]) (sq_nonneg _)

/-- A common small budget pays the two multiplicative and one additive errors. -/
theorem fouvryG9Low_final_budget (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/4 ∧
      4*(1+κ)^2*(B+κ)+κ ≤ 4*B+τ := by
  let κ := min (1/4) (τ/(100*(B+1)))
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκu : κ ≤ 1/4 := min_le_left _ _
  have hκτ : κ*(100*(B+1)) ≤ τ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have h2 : κ^2 ≤ κ := by nlinarith
  have hsq : (1+κ)^2 ≤ 1+3*κ := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ B+κ by positivity)
  refine ⟨κ,hκ,hκu,?_⟩
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
