import Wu18938Campaign.M6.PhysicalOutput
import WR2FouvryPaid
import U8MeshFamily
import OriginalNormalized

noncomputable section
open Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace Wu18938Campaign.M6

theorem high_prefix_paid (A : ℕ) {e ε δ η ρ σ : ℝ}
    (he : (3 / 4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100 / 1327) (hεδ : ε < δ) (hδ : δ < 1 / 2)
    (hη : 0 < η) (hηu : η < 1 / 8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) → z ≤ Real.sqrt N →
      ((U8Literal.physicalPrefix N e).card : ℝ) ≤
        (∑ k ∈ U8Literal.occupied N e ρ, OriginalU8.actualCenter N ρ δ η k P z) +
          σ * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨Ts, hs⟩ := WuPaper.R2Fouvry.original_physical_prefix_paid (A + 4)
    he he1 hε hεa hεδ hδ hη hηu
  obtain ⟨Tm, hm⟩ := U8Literal.Mesh.mesh_log_payment A hρ
    (by norm_num : (0 : ℝ) ≤ 1) (half_pos hσ)
  obtain ⟨To, _, ho⟩ := outputBad_log_paid A (half_pos hσ)
  refine ⟨max Ts (max Tm (To : ℝ)), ?_⟩
  intro N hN P hP hPN z hcut hz
  have hNs := (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hNm := (le_max_left _ _).trans hr
  have hNo : To ≤ N := by exact_mod_cast (le_max_right _ _).trans hr
  have hp := hs N hNs ρ hρ hρu P hP hPN z hcut
  have hmesh := hm N hNm e (fun _ => (N : ℝ) / (Real.log N) ^ (A + 4))
    (by intro k hk; simp only [one_mul])
  simp only [sum_const, nsmul_eq_mul] at hmesh
  have hout := ho N hNo e P hP (fun p hp => (hcut p hp).trans_le hz)
  change ((U8Literal.physicalPrefix N e).card : ℝ) ≤
    (∑ k ∈ U8Literal.occupied N e ρ, OriginalU8.actualCenter N ρ δ η k P z) +
      ((U8Literal.occupied N e ρ).card : ℝ) * ((N : ℝ) / (Real.log N) ^ (A + 4)) +
      (U8Literal.outputBad N e P).card at hp
  linarith

theorem high_prefix_normalized (τ : ℝ) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 8 ∧ ∀ (A : ℕ) (e ε δ ρ σ : ℝ),
      (3 / 4 : ℝ) ≤ e → e ≤ 1 → 0 < ε → ε < 100 / 1327 →
      ε < δ → δ < 1 / 4 → 1 < ρ → ρ ≤ 5 / 4 → 0 < σ →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      ((U8Literal.physicalPrefix N e).card : ℝ) ≤
        4 * (1 + τ) * SingularSeries.liuSingularSeries N *
          (∑ k ∈ U8Literal.occupied N e ρ,
            OriginalU8.rectangleMass N ρ k / Real.log (OriginalU8.level N ρ δ k)) +
          σ * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨η, hη, hηu, hdensity⟩ := OriginalU8.actualCenter_normalized τ hτ
  refine ⟨η, hη, hηu, ?_⟩
  intro A e ε δ ρ σ he he1 hε hεa hεδ hδ hρ hρu hσ
  obtain ⟨Td, hd⟩ := hdensity δ (by linarith) hδ
  obtain ⟨Tp, hp⟩ := high_prefix_paid A he he1 hε hεa hεδ (by linarith)
    hη hηu hρ hρu hσ
  refine ⟨max 1 (max Td Tp), ?_⟩
  intro N hN hEven
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hNd := (le_max_left _ _).trans hr
  have hNp := (le_max_right _ _).trans hr
  have he0 : 0 < e := by linarith
  have hcount := hp N hNp (fouvryG9SievePrimes N (Real.sqrt N))
    (fun p hp => ((fouvryG9SievePrimes_mem N p _).mp hp).1)
    (fun p hp => ((fouvryG9SievePrimes_mem N p _).mp hp).2.1)
    (Real.sqrt N) (fun p hp => ((fouvryG9SievePrimes_mem N p _).mp hp).2.2) le_rfl
  apply hcount.trans
  apply add_le_add_right
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hcell := hd N hNd hEven e ρ he0 hρ hρu k
    (U8Literal.Join.occupied_to_original hN1 hρ hk)
  exact hcell.trans_eq (by ring)

end Wu18938Campaign.M6
