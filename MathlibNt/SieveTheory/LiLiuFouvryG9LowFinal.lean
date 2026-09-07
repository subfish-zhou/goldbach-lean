import MathlibNt.SieveTheory.LiLiuFouvryG9S5Kernel
import MathlibNt.SieveTheory.LiLiuFouvryG9KernelBudget

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual low-first-prime S5 bound with the literal weighted integral.
All sieve, distribution, prefix, mesh and perturbation parameters are internal.
The product-window e is fixed before the natural-number threshold. -/
theorem fouvryG9S5Low_integral_upper (τ : ℝ) (hτ : 0 < τ)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N e) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^(1/10 : ℝ)) : ℝ) ≤
        ((36/5 : ℝ)*fouvryG9RelaxedIntegralLow+τ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  let B : ℝ := (9/5 : ℝ)*fouvryG9RelaxedIntegralLow
  have hB : 0 ≤ B := mul_nonneg (by norm_num) fouvryG9LowIntegral_nonneg
  obtain ⟨κ,hκ,_,hbudget⟩ := fouvryG9Low_final_budget B τ hB hτ
  obtain ⟨δ,hδ0,hδ,ρ,hρ,hρu,hkernel⟩ := fouvryG9RelaxedPairKernel_final κ hκ
  obtain ⟨Nk,hk⟩ := hkernel δ hδ0.le le_rfl ρ hρ le_rfl
  let ε : ℝ := min (δ/2) (2/53)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεa : ε < 4/53 := (min_le_right _ _).trans_lt (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨Ns,hs⟩ := fouvryG9S5Low_kernel_upper κ κ κ hκ hκ hκ
    he he1 hε hεa hεδ hδ hρ hρu
  refine ⟨max 4 (max Nk ⌈Ns⌉₊),le_max_left _ _,?_⟩
  intro N hN hEven
  have hN' := (le_max_right _ _).trans hN
  have hNk : Nk ≤ N := (le_max_left _ _).trans hN'
  have hceil : ⌈Ns⌉₊ ≤ N := (le_max_right _ _).trans hN'
  have hNs : Ns ≤ (N : ℝ) := (Nat.le_ceil Ns).trans (by exact_mod_cast hceil)
  have hsN := hs N hNs hEven
  have hK := hk N hNk
  change ρ^3*fouvryG9RelaxedPairKernel N ρ δ ≤ B+κ at hK
  have hcoeff : 4*(1+κ)*(1+κ)*(ρ^3*fouvryG9RelaxedPairKernel N ρ δ)+κ ≤
      (36/5 : ℝ)*fouvryG9RelaxedIntegralLow+τ := by
    calc
      _ = 4*(1+κ)^2*(ρ^3*fouvryG9RelaxedPairKernel N ρ δ)+κ := by ring
      _ ≤ 4*(1+κ)^2*(B+κ)+κ :=
        add_le_add (mul_le_mul_of_nonneg_left hK (by positivity)) le_rfl
      _ ≤ 4*B+τ := hbudget
      _ = _ := by dsimp [B]; ring
  have hscale : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 := by
    have := (SingularSeries.liuSingularSeries_pos N).le
    positivity
  exact hsN.trans (mul_le_mul_of_nonneg_right hcoeff hscale)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
