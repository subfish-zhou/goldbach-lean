import MathlibNt.SieveTheory.LiLiuFouvryG9EulerEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9BaseEuler
import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutputPrime

noncomputable section
open Finset
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Original prime-output mother bounded by actual labelled rectangle mass.
The small-output correction, actual Euler correction and distribution remainder
are proved, rather than supplied as target-shaped hypotheses. -/
theorem fouvryG9PrimeOutput_mass_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
      ∀ A : ℕ, ∀ e ε δ η ρ : ℝ,
      0 < e → e ≤ 1 → 0 < ε → ε < 4/53 → ε < δ → δ < 1/4 →
      0 < η → η < 1/8 → 1 < ρ → ρ ≤ 5/4 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      fouvryG9MotherPrimeOutput N e ≤
        (∑ k ∈ fouvryG9GridUsed N e ρ,
          fouvryG9UpperFactor N
            ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) C K η *
          (fouvryG9BaseEuler N (Real.sqrt N)*
            (1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3*fouvryG9RectangleMass N ρ k)) +
              (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,hC,K,hK,hmain⟩ := fouvryG9RectangleMain_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro A e ε δ η ρ he he1 hε hεa hεδ hδ hη hηu hρ hρu
  obtain ⟨Ns,hs⟩ := fouvryG9MotherPrimeOutput_total A he he1 hε hεa hεδ
    (by linarith) hη hηu hρ hρu
  obtain ⟨Nm,hm⟩ := hmain δ η (hε.le.trans hεδ.le) hδ hη hηu
  obtain ⟨Ne,heuler⟩ := g9_actual_weighted_euler_eventually he
  refine ⟨max Ns (max Nm Ne),?_⟩
  intro N hN hEven
  have hNs := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNm := (le_max_left _ _).trans hrest
  have hNe := (le_max_right _ _).trans hrest
  apply (hs N hNs (Real.sqrt N) (Real.sqrt_nonneg _) le_rfl).trans
  apply add_le_add _ le_rfl
  apply sum_le_sum
  intro k hk
  have hne := fouvryG9GridCell_nonempty_iff.mpr hk
  obtain ⟨hfactor,hrect⟩ := hm N hNm hEven e ρ he hρ hρu k hne
  exact hrect.trans (mul_le_mul_of_nonneg_left
    (heuler N hNe ρ hρ hρu k hne (fouvryG9SievePrimes N (Real.sqrt N))
      (fouvryG9SievePrimes_odd hEven _)) hfactor)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
