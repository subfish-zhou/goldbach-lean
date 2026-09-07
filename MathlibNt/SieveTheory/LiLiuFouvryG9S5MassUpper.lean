import MathlibNt.SieveTheory.LiLiuFouvryG9SiftedMassUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9LiteralMother

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original low S5 count reaches actual rectangle mass through the existing
switching-cost producer and the exact literal mother identity. Analytic mass
and scalar normalization remain visible; this is not yet the paper integral. -/
theorem fouvryG9S5Low_mass_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
      ∀ A : ℕ, ∀ e ε δ η ρ ζ : ℝ,
      0 < e → e ≤ 1 → 0 < ε → ε < 4/53 → ε < δ → δ < 1/4 →
      0 < η → η < 1/8 → 1 < ρ → ρ ≤ 5/4 → 0 < ζ →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N e) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^(1/10 : ℝ)) : ℝ) ≤
        (∑ k ∈ fouvryG9GridUsed N e ρ,
          fouvryG9UpperFactor N
            ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) C K η *
          (fouvryG9BaseEuler N (Real.sqrt N)*
            (1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3*fouvryG9RectangleMass N ρ k)) +
              (N : ℝ)/Real.log (N : ℝ)^A +
                ζ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨C,hC,K,hK,hm⟩ := fouvryG9Sifted_mass_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro A e ε δ η ρ ζ he he1 hε hεa hεδ hδ hη hηu hρ hρu hζ
  obtain ⟨Nm,hm⟩ := hm A e ε δ η ρ he he1 hε hεa hεδ hδ hη hηu hρ hρu
  obtain ⟨Ns,hNs,hs⟩ := goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos e ζ he hζ
  refine ⟨max Nm (Ns : ℝ),?_⟩
  intro N hN hEven
  have hmN := (le_max_left _ _).trans hN
  have hsN : Ns ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hroot : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN1
  have h := hs N hsN (Real.sqrt N) hroot le_rfl
  rw [← fouvryG9MotherSifted_eq_original] at h
  exact h.trans (add_le_add (hm N hmN hEven) le_rfl)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
