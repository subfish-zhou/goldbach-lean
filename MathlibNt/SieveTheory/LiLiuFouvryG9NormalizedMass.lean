import MathlibNt.SieveTheory.LiLiuFouvryG9S5MassUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Nonnegativity of the actual labelled rectangle mass. -/
theorem fouvryG9RectangleMass_nonneg (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) :
    0 ≤ fouvryG9RectangleMass N ρ k := by
  apply sum_nonneg
  intro m _
  apply sum_nonneg
  intro n _
  exact mul_nonneg (fouvryG9LongAlpha_nonneg N ρ k m)
    (fouvryG9_prime_copN_beta_bounds N n).1

/-- The original low S5 count, with all sieve-scalar and Euler corrections paid.
Only the explicitly displayed weighted prime-rectangle mass remains analytic. -/
theorem fouvryG9S5Low_normalized_mass_upper (τ : ℝ) (hτ : 0 < τ) :
    ∀ A : ℕ, ∀ e ε δ ρ ζ : ℝ,
      0 < e → e ≤ 1 → 0 < ε → ε < 4/53 → ε < δ → δ < 1/4 →
      1 < ρ → ρ ≤ 5/4 → 0 < ζ →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N e) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^(1/10 : ℝ)) : ℝ) ≤
        4*(1+τ)*SingularSeries.liuSingularSeries N *
          (∑ k ∈ fouvryG9GridUsed N e ρ,
            fouvryG9RectangleMass N ρ k /
              Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ)))) +
          (N : ℝ)/Real.log (N : ℝ)^A +
          ζ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨C,hC,K,hK,hm⟩ := fouvryG9S5Low_mass_upper
  obtain ⟨η,hη,hηu,hpay⟩ := fouvryG9MainScalar_payment C K τ hC hK hτ
  intro A e ε δ ρ ζ he he1 hε hεa hεδ hδ hρ hρu hζ
  obtain ⟨Nm,hm⟩ := hm A e ε δ η ρ ζ he he1 hε hεa hεδ hδ hη hηu hρ hρu hζ
  obtain ⟨Nq,hq⟩ := hpay δ (by linarith) hδ
  obtain ⟨Ng,hg⟩ := eventually_atTop.1
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  refine ⟨max Nm (max Nq Ng),?_⟩
  intro N hN hEven
  have hmN := (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hqN := (le_max_left _ _).trans hr
  have hgN := (le_max_right _ _).trans hr
  have hsix : 6 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hg N hgN
  apply (hm N hmN hEven).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hne := fouvryG9GridCell_nonempty_iff.mpr hk
  obtain ⟨_,_,_,hlo,hhi⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  have hp := hq N hqN hEven ((2/3 : ℝ)*ρ^k.1) hT hhi
  calc
    _ = (fouvryG9BaseEuler N (Real.sqrt N)*(1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3 *
        fouvryG9UpperFactor N ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) C K η) *
        fouvryG9RectangleMass N ρ k := by ring
    _ ≤ (4*(1+τ)*SingularSeries.liuSingularSeries N /
        Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ)))) *
        fouvryG9RectangleMass N ρ k :=
      mul_le_mul_of_nonneg_right hp (fouvryG9RectangleMass_nonneg N ρ k)
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
