import U8SingleLineageJoin
import OriginalPayment
import U8MeshPayment
import U8LowOutput

noncomputable section
open Finset
namespace U8Literal.Mesh.Consumer

/-- Common P and z are merely the constant-family specialization. -/
theorem constant_family_lowPaid (A : ℕ) {e ε δ η ρ σ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ P : Finset ℕ, ∀ z : ℝ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      (∀ p ∈ P, (p : ℝ) < z) → z ≤ Real.sqrt (N : ℝ) →
      ((physicalSmall N).card : ℝ) ≤
        (∑ k ∈ occupied N e ρ, externalCenter N ρ δ η k P z) +
          σ*(N : ℝ)/Real.log (N : ℝ)^A + (smallPrefix N e).card := by
  obtain ⟨M,hM⟩ := physicalSmall_lowPaid A he he1 hε hεa hεδ hδ hη hηu hρ hρu hσ
  refine ⟨M, ?_⟩
  intro N hN P z hP hPN hcut hZ
  exact hM N hN (fun _ => P) (fun _ => z) (fun _ _ => hP)
    (fun _ _ => hPN) (fun _ _ => hcut) (fun _ _ => hZ)

end U8Literal.Mesh.Consumer
