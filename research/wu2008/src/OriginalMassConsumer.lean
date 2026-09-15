import MeshConsumer
import OriginalNormalized

noncomputable section
open Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

theorem externalCenter_eq_actual (N : ℕ) (ρ δ η : ℝ)
    (k : U8Literal.Key) (P : Finset ℕ) (z : ℝ) :
    U8Literal.Mesh.externalCenter N ρ δ η k P z = actualCenter N ρ δ η k P z := rfl

/-- The actual physical small window: the fixed-e prefix is never absorbed.
The density choice precedes every distribution and mesh parameter. -/
theorem physicalSmall_normalized (τ : ℝ) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧ ∀ (A : ℕ) (δ ε e ρ σ : ℝ),
      0 < ε → ε < 100/1327 → ε < δ → δ < 1/4 →
      0 < e → e ≤ 1 → 1 < ρ → ρ ≤ 5/4 → 0 < σ →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      ((U8Literal.physicalSmall N).card : ℝ) ≤
        4*(1+τ)*SingularSeries.liuSingularSeries N *
          (∑ k ∈ U8Literal.occupied N e ρ, rectangleMass N ρ k / Real.log (level N ρ δ k)) +
          σ*(N : ℝ)/Real.log (N : ℝ)^A + (U8Literal.smallPrefix N e).card := by
  obtain ⟨η,hη,hηu,hd⟩ := actualCenter_normalized τ hτ
  refine ⟨η,hη,hηu,?_⟩
  intro A δ ε e ρ σ hε hεa hεδ hδ he he1 hρ hρu hσ
  obtain ⟨Nd,hd⟩ := hd δ (hε.le.trans hεδ.le) hδ
  obtain ⟨Nm,hm⟩ := U8Literal.Mesh.Consumer.constant_family_lowPaid A
    he he1 hε hεa hεδ (by linarith) hη hηu hρ hρu hσ
  refine ⟨max 1 (max Nd Nm),?_⟩
  intro N hN hEven
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNd := (le_max_left _ _).trans hrest
  have hNm := (le_max_right _ _).trans hrest
  have h := hm N hNm (fouvryG9SievePrimes N (Real.sqrt N)) (Real.sqrt N)
    (fun p hp => (fouvryG9SievePrimes_mem N p _).mp hp |>.1)
    (fun p hp => (fouvryG9SievePrimes_mem N p _).mp hp |>.2.1)
    (fun p hp => (fouvryG9SievePrimes_mem N p _).mp hp |>.2.2) le_rfl
  apply h.trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  rw [externalCenter_eq_actual]
  have hb := hd N hNd hEven e ρ he hρ hρu k
    (U8Literal.Join.occupied_to_original hN1 hρ hk)
  calc
    _ ≤ _ := hb
    _ = _ := by ring

end OriginalU8
