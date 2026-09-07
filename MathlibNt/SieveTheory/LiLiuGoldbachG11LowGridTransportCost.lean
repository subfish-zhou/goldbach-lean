import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridCost
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment

open Finset Filter
open scoped BigOperators Classical
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- All elementary source gates are internal and uniform in the retained epsilon. -/
theorem goldbachG11LowGrid_internal_gates {δ θ ρ : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hθ : 0 < θ)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ ε : ℝ,
      ∀ k ∈ goldbachG11LowGridUsed N ε ρ,
      1 ≤ (N : ℝ) ∧ 4 ≤ (N : ℝ)^(4/53 : ℝ) ∧
      1 ≤ goldbachG11GridLowLevel N δ ρ k ∧
      2 ≤ externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ ∧
      goldbachG11GridLowLevel N δ ρ k ≤ N := by
  obtain ⟨Ng,hg⟩ := g9WF_exists_internal_level_gate hδ hδu hθ 1
  obtain ⟨Nb,hb⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max Ng Nb,?_⟩
  intro N hN ε k hk
  obtain ⟨hNg,hNb⟩ := max_le_iff.mp hN
  have hbig := hb N hNb
  have hTlo := goldbachG11Grid_short_scale_lower hρ hρu (mem_filter.mp hk).1
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  obtain ⟨hn,hq,_hq0,hd,hqn⟩ := hg N ((2/3)*ρ^k.1) hNg hT
    (goldbachG11LowGrid_short_upper hρ hk)
  exact ⟨hn,hbig,hq,hd,hqn⟩

/-- A common envelope for the actual primorial-to-full costs, after the tag
cardinality bound, at the original N-relative level. -/
def goldbachG11LowGridTransportEnvelope (N : ℕ) (ε δ θ ρ C : ℝ) : ℝ :=
  ∑ k ∈ goldbachG11LowGridUsed N ε ρ,
    Real.exp (8*(θ⁻¹)^3)*(C*(N : ℝ)^(1+g9TransportMu δ θ))*
      (4/(externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ)^(θ^2))*
      (1+Real.log (⌊goldbachG11GridLowLevel N δ ρ k⌋₊ : ℝ))^2

theorem goldbachG11LowGrid_transport_envelope_paid (A : ℕ) {δ θ ρ C : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hθ : 0 < θ) (hθu : θ < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hC : 0 < C) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ ε : ℝ,
      goldbachG11LowGridTransportEnvelope N ε δ θ ρ C ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
  let G : ℝ := (1/Real.log ρ+1)^3
  let B : ℝ := 16*Real.exp (8*(θ⁻¹)^3)*C
  let μ := g9TransportMu δ θ
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (g9Transport_eventually_envelope (G*B) A (g9TransportMu_pos hδu hθ))
  obtain ⟨Ng,hg⟩ := goldbachG11LowGrid_internal_gates hδ hδu hθ hρ hρu
  refine ⟨max M Ng,?_⟩
  intro N hN ε
  obtain ⟨hNM,hNg⟩ := max_le_iff.mp hN
  obtain ⟨hN1,hlog,hpay⟩ := hM N hNM
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn : (0 : ℝ) < N := by linarith
  have hln : 0 < Real.log (N : ℝ) := by linarith
  have hpoint : ∀ k ∈ goldbachG11LowGridUsed N ε ρ,
      1 ≤ (2/3 : ℝ)*ρ^k.1 := by
    intro k hk
    have hb := (hg N hNg ε k hk).2.1
    have ht := goldbachG11Grid_short_scale_lower hρ hρu (mem_filter.mp hk).1
    linarith
  unfold goldbachG11LowGridTransportEnvelope
  calc
    _ ≤ ∑ _k ∈ goldbachG11LowGridUsed N ε ρ,
        B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2 := by
      apply sum_le_sum
      intro k hk
      exact g9Transport_one hN1 hlog (hpoint k hk)
        (goldbachG11LowGrid_short_upper hρ hk) hδ hδu hθ hθu hC.le
    _ = ((goldbachG11LowGridUsed N ε ρ).card : ℝ)*
        (B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) := by simp
    _ ≤ (G*Real.log (N : ℝ)^3)*(B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (goldbachG11LowGridCost_card hρ hlog) (by positivity)
    _ = (G*B)*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^5 := by ring
    _ ≤ _ := hpay

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig