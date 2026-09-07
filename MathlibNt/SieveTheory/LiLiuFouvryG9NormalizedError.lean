import MathlibNt.SieveTheory.LiLiuFouvryG9NormalizedMass

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The remaining log-cubed additive error is small on the true Liu scale,
using the already proved positive uniform lower bound for the singular series. -/
theorem fouvryG9_logCube_error_payment {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (N : ℝ)/Real.log (N : ℝ)^3 ≤
        ζ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  let D := ζ*SingularSeries.liuUniversalProduct
  have hD : 0 < D := mul_pos hζ SingularSeries.liuUniversalProduct_pos
  refine ⟨Real.exp (max 1 (1/D)),?_⟩
  intro N hN
  have hn := Real.log_le_log (Real.exp_pos (max 1 (1/D))) hN
  rw [Real.log_exp] at hn
  have hl1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hn
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have hlD : 1/D ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hn
  have hmul : 1 ≤ D*Real.log (N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hD).mp hlD
  have hrec : 1/Real.log (N : ℝ) ≤ ζ*SingularSeries.liuSingularSeries N := by
    apply ((div_le_iff₀ hl0).mpr hmul).trans
    exact mul_le_mul_of_nonneg_left (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hζ.le
  calc
    _ = ((N : ℝ)/Real.log (N : ℝ)^2)*(1/Real.log (N : ℝ)) := by ring
    _ ≤ ((N : ℝ)/Real.log (N : ℝ)^2)*(ζ*SingularSeries.liuSingularSeries N) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = _ := by ring

/-- A single remaining analytic object: the actual occupied weighted mass.
All other errors have been absorbed on the original singular-series scale. -/
theorem fouvryG9S5Low_weighted_mass_upper (τ ζ : ℝ) (hτ : 0 < τ) (hζ : 0 < ζ)
    {e ε δ ρ : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 4/53) (hεδ : ε < δ) (hδ : δ < 1/4)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N e) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^(1/10 : ℝ)) : ℝ) ≤
        4*(1+τ)*SingularSeries.liuSingularSeries N *
          (∑ k ∈ fouvryG9GridUsed N e ρ,
            fouvryG9RectangleMass N ρ k /
              Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ)))) +
          ζ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨Nm,hm⟩ := fouvryG9S5Low_normalized_mass_upper τ hτ 3 e ε δ ρ (ζ/2)
    he he1 hε hεa hεδ hδ hρ hρu (by positivity)
  obtain ⟨Ne,he'⟩ := fouvryG9_logCube_error_payment (by positivity : 0 < ζ/2)
  refine ⟨max Nm Ne,?_⟩
  intro N hN hEven
  have hmN := hm N ((le_max_left _ _).trans hN) hEven
  have heN := he' N ((le_max_right _ _).trans hN)
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
