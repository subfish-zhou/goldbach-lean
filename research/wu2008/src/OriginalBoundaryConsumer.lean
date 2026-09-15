import OriginalBoundaryFTC

noncomputable section
open Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8.Weighted

/-- Whole-domain weighted mass on the original N/log^2 N scale.  The PNT
slack is explicit, and the rho cube is paid by the actual kernel producer. -/
theorem original_mass_integral (τ ζ : ℝ) (hτ : 0 < τ) (hζ : 0 < ζ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1/4 ∧
      ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ρ₀ ≤ 5/4 ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ → ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ₀ →
          ∀ e : ℝ, 0 < e → ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
            (∑ k ∈ U8Literal.occupied N e ρ,
              rectangleMass N ρ k / Real.log (level N ρ δ k)) ≤
              (1+ζ)*((9/5 : ℝ)*low (100/1327)+τ)*((N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨δ₀,hδ₀,hδ₀u,ρ₀,hρ₀,hρ₀u,hK⟩ := original_kernel_final τ hτ
  refine ⟨δ₀,hδ₀,hδ₀u,ρ₀,hρ₀,hρ₀u,?_⟩
  intro δ hδ0 hδ ρ hρ hρu e he
  obtain ⟨Nk,hNk⟩ := hK δ hδ0 hδ ρ hρ hρu
  obtain ⟨Nm,hNm⟩ := original_rectangleMass_le_kernel he hρ (hρu.trans hρ₀u)
    (hδ.trans_lt hδ₀u) hζ
  refine ⟨max Nm (Nk : ℝ), fun N hN => ?_⟩
  have hk := hNk N (by exact_mod_cast (le_max_right _ _).trans hN)
  have hm := hNm N ((le_max_left _ _).trans hN)
  have hc : 0 ≤ (1+ζ)*((N : ℝ)/Real.log (N : ℝ)^2) := by positivity
  calc
    _ ≤ _ := hm
    _ = ((1+ζ)*((N : ℝ)/Real.log (N : ℝ)^2))*(ρ^3*relaxedPairKernel N ρ δ) := by ring
    _ ≤ ((1+ζ)*((N : ℝ)/Real.log (N : ℝ)^2))*((9/5 : ℝ)*low (100/1327)+τ) :=
      mul_le_mul_of_nonneg_left hk hc
    _ = _ := by ring

/-- The already proved physical consumer is used once, without rebuilding its
finite geometry, sieve, density, or mesh error.  The small prefix stays visible. -/
theorem physicalSmall_integral (τ ζ θ : ℝ) (hτ : 0 < τ) (hζ : 0 < ζ) (hθ : 0 < θ) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1/4 ∧
        ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ρ₀ ≤ 5/4 ∧
          ∀ (A : ℕ) (δ ε e ρ σ : ℝ),
            0 < ε → ε < 100/1327 → ε < δ → δ ≤ δ₀ →
            0 < e → e ≤ 1 → 1 < ρ → ρ ≤ ρ₀ → 0 < σ →
            ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
              ((U8Literal.physicalSmall N).card : ℝ) ≤
                4*(1+θ)*(1+ζ)*SingularSeries.liuSingularSeries N *
                  ((9/5 : ℝ)*low (100/1327)+τ)*((N : ℝ)/Real.log (N : ℝ)^2) +
                  σ*(N : ℝ)/Real.log (N : ℝ)^A + (U8Literal.smallPrefix N e).card := by
  obtain ⟨η,hη,hηu,hP⟩ := physicalSmall_normalized θ hθ
  obtain ⟨δ₀,hδ₀,hδ₀u,ρ₀,hρ₀,hρ₀u,hM⟩ := original_mass_integral τ ζ hτ hζ
  refine ⟨η,hη,hηu,δ₀,hδ₀,hδ₀u,ρ₀,hρ₀,hρ₀u,?_⟩
  intro A δ ε e ρ σ hε hεa hεδ hδ he he1 hρ hρu hσ
  have hδ0 : 0 ≤ δ := hε.le.trans hεδ.le
  obtain ⟨Np,hNp⟩ := hP A δ ε e ρ σ hε hεa hεδ (hδ.trans_lt hδ₀u)
    he he1 hρ (hρu.trans hρ₀u) hσ
  obtain ⟨Nm,hNm⟩ := hM δ hδ0 hδ ρ hρ hρu e he
  refine ⟨max Np Nm, fun N hN hEven => ?_⟩
  have hp := hNp N ((le_max_left _ _).trans hN) hEven
  have hm := hNm N ((le_max_right _ _).trans hN)
  have hS := (SingularSeries.liuSingularSeries_pos N).le
  have hc : 0 ≤ 4*(1+θ)*SingularSeries.liuSingularSeries N := by positivity
  apply hp.trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  calc
    _ ≤ (4*(1+θ)*SingularSeries.liuSingularSeries N)*
        ((1+ζ)*((9/5 : ℝ)*low (100/1327)+τ)*((N : ℝ)/Real.log (N : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hm hc
    _ = _ := by ring

/-- The factor eight is derived from the actual density four and kernel 9/5.
It is not a definition of a rescaled integral masquerading as the original one. -/
theorem original_eight_normalization (N : ℕ) :
    4*SingularSeries.liuSingularSeries N*((9/5 : ℝ)*low (100/1327))*
      ((N : ℝ)/Real.log (N : ℝ)^2) =
    8*SingularSeries.liuSingularSeries N*((N : ℝ)/Real.log (N : ℝ)^2)*
      ((9/10 : ℝ)*(∫ x in (100/1327 : ℝ)..(1/10),
        Real.log (2-3*x)/(x*(1-x)^2))) := by
  rw [original_low_eq_single]
  ring

end OriginalU8.Weighted
