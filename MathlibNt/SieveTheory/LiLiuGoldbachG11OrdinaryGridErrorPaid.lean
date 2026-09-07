import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridSource
import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryLevel

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11OrdinaryGridError (N : ℕ) (ε ρ δ : ℝ) : ℝ :=
  ∑ k ∈ goldbachG11GridUsed N ε ρ,
    ∑ d ∈ goldbachG11LinkedModuli N ⌊goldbachG11OrdinaryLevel N δ⌋₊,
      |goldbachG11OrdinaryRectangleResidual N ε ρ k d N|

/-- All actual ordinary-grid errors are paid at the original half-minus-delta
level. Any fixed external-family cardinality is also paid; epsilon is after N0. -/
theorem goldbachG11OrdinaryGrid_error_total (A : ℕ) (F : ℝ) (hF : 0 ≤ F)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ,
      F*goldbachG11OrdinaryGridError N ε ρ δ ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨B,C,hB,hC,Ms,hMs,hs⟩ := goldbachG11OrdinaryRectangleResidual_squarefree
    ((A+4 : ℕ) : ℝ) (by positivity)
  obtain ⟨Ml,_hMl,hl⟩ := goldbachG11OrdinaryLevel_in_source B hδ
  let G : ℝ := (1/Real.log ρ+1)^3
  let L : ℝ := max 1 (G*(F*C))
  refine ⟨max Ms (max Ml ⌈Real.exp L⌉₊),hMs.trans (le_max_left _ _),?_⟩
  intro N hN ε
  obtain ⟨hNs,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hNl,hNe⟩ := max_le_iff.mp hrest
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hMs.trans hNs
  have hn : (0 : ℝ) < N := by linarith
  have he : Real.exp L ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
  have hL : L ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hn).2 he
  have hlog : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hpay : G*(F*C) ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL
  have hlogcmp : Real.log (N : ℝ) ≤ Real.log (4*(N : ℝ)) :=
    Real.log_le_log hn (by linarith)
  have hQ : (⌊goldbachG11OrdinaryLevel N δ⌋₊ : ℝ) ≤
      Real.sqrt (4*(N : ℝ))/Real.log (4*(N : ℝ))^B :=
    (Nat.floor_le (Real.rpow_nonneg hn.le _)).trans (hl N hNl)
  let E := fun k => ∑ d ∈ goldbachG11LinkedModuli N ⌊goldbachG11OrdinaryLevel N δ⌋₊,
    |goldbachG11OrdinaryRectangleResidual N ε ρ k d N|
  have hrow : ∀ k ∈ goldbachG11GridUsed N ε ρ, E k ≤ C*N/Real.log (N : ℝ)^(A+4) := by
    intro k hk
    have hh := hs N hNs ε ρ hρ hρu k hk ⌊goldbachG11OrdinaryLevel N δ⌋₊ hQ
    rw [Real.rpow_natCast] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by positivity)
      (pow_pos hlogpos (A+4)) (pow_le_pow_left₀ hlogpos.le hlogcmp (A+4)))
  have hsum := sum_le_sum hrow
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hcard : ((goldbachG11GridUsed N ε ρ).card : ℝ) ≤ G*Real.log (N : ℝ)^3 :=
    goldbachG11GridCost_card hρ hlog
  change F*(∑ k ∈ goldbachG11GridUsed N ε ρ,E k) ≤ _
  calc
    _ ≤ F*(((goldbachG11GridUsed N ε ρ).card : ℝ)*(C*N/Real.log (N : ℝ)^(A+4))) :=
      mul_le_mul_of_nonneg_left hsum hF
    _ ≤ F*((G*Real.log (N : ℝ)^3)*(C*N/Real.log (N : ℝ)^(A+4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (by positivity)) hF
    _ = (G*Real.log (N : ℝ)^3)*((F*C)*N/Real.log (N : ℝ)^(A+4)) := by ring
    _ ≤ _ := fouvryG9GridCost_scalar A hn.le hlogpos hpay

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig