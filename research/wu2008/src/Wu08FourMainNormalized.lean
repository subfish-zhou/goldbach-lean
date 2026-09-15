import Wu08FourMainWeight

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.Normalization

/-- Actual finite rectangle masses, still retaining every long labelled rough
integer. These are NOT yet continuous integrals. -/
def plainGridMass (N : ℕ) (e : Bool) (ξ ρ : ℝ) : ℝ :=
  ∑ k ∈ occupied N e ξ ρ, cellMass N e ξ ρ k

def weightedGridMass (N : ℕ) (e : Bool) (ξ ρ : ℝ) : ℝ :=
  ∑ k ∈ occupied N e ξ ρ, cellWeight N ρ k*cellMass N e ξ ρ k

theorem cellMass_nonneg (N : ℕ) (e : Bool) (ξ ρ : ℝ) (k : Key) :
    0 ≤ cellMass N e ξ ρ k :=
  sum_nonneg (fun m _ => sum_nonneg (fun a _ => mul_nonneg (alpha_nonneg _ m) (beta_nonneg N a)))

/-- Full actual properMain has now been normalized to Wu's small-prime weight
with explicit vanishing parameter loss. No error previously paid is reopened. -/
theorem properMain_weighted_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ δ η ζ : ℝ,
    0 ≤ δ → δ < 1/4 → 0 < η → η < 1/8 → 0 < ζ →
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
    ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
      properMain N e ξ ρ δ η ≤ (1+ζ)^2*(wuSingularSeries N/log N)*
        (weightedGridMass N e ξ ρ+
          (32*δ+4*exp (-eulerMascheroniConstant)*C*η+ζ)*plainGridMass N e ξ ρ) := by
  obtain ⟨C,hC,K,_,hmain⟩ := properMain_density_upper
  refine ⟨C,hC,?_⟩
  intro δ η ζ hδ hδu hη hηu hζ
  obtain ⟨Nm,hm⟩ := hmain δ η hδ hδu hη hηu
  obtain ⟨Ng,hg⟩ := occupied_level_gate hδ hδu hη 4
  obtain ⟨Ne,he⟩ := fullEulerCorrection_eventually hζ
  obtain ⟨Nf,hf⟩ := familyDefect_eventually C K η hζ
  obtain ⟨Nb,hb⟩ := fouvryG9BaseEuler_sqrt_upper ζ hζ
  refine ⟨max 4 (max Nm (max Ng (max Ne (max Nf Nb)))),?_⟩
  intro N hN hEven e ξ ρ hξ hρ hρu
  have hn4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hn0 : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hln : 0 < log (N : ℝ) := log_pos (by linarith)
  have hNm := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNg := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNe := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hNf := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))))
  have hNb := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))))
  obtain ⟨hfac,hbound⟩ := hm N hNm hEven e ξ ρ hξ hρ hρu
  let F := fun k => fouvryG9UpperFactor N (level N ρ δ k) C K η
  let S := wuSingularSeries N/log N
  let H := 4*exp (-eulerMascheroniConstant)
  let E := 32*δ+H*C*η+ζ
  have hS : 0 ≤ S := by
    dsimp [S]
    rw [wuSingularSeries_eq_liu N hn0]
    exact div_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le hln.le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc : fullEulerCorrection N ≤ 1+ζ := he N hNe
  have hlocal : ∀ k ∈ occupied N e ξ ρ,
      H*F k ≤ cellWeight N ρ k+E := by
    intro k hk
    obtain ⟨_,_,hT,_,hq,hqN,_,_⟩ := hg N hNg e ξ ρ hξ hρ hρu k hk
    have hTu := (occupied_geometry hξ hρ hρu hk).2.2.2.2
    obtain ⟨hlow,hweight⟩ := level_weight_loss hn4 hδ hδu hT hTu
    have hlq : 0 < log (level N ρ δ k) := log_pos (by linarith)
    have hnorm := upperFactor_scaled (C := C) (K := K) (η := η)
      hn4 (by linarith : 0 < level N ρ δ k) hlq hqN
    have hdef := hf N hNf _ hlow
    dsimp only [H,F,E]
    rw [hnorm]
    linarith only [hweight,hdef]
  have hrawEuler : fouvryG9BaseEuler N (sqrt N) ≤ H*(1+ζ)*S := by
    have hh := (le_div_iff₀ hln).mpr (hb N hNb hEven)
    dsimp only [H,S]
    rw [wuSingularSeries_eq_liu N hn0]
    exact hh.trans_eq (by ring)
  have hsum0 : 0 ≤ ∑ k ∈ occupied N e ξ ρ, F k*cellMass N e ξ ρ k :=
    sum_nonneg (fun k hk => mul_nonneg (hfac k hk) (cellMass_nonneg _ _ _ _ _))
  have hb0 : 0 ≤ fouvryG9BaseEuler N (sqrt N) :=
    g9_baseEuler_nonneg (properPrimes N) (fun p hp => (fouvryG9SievePrimes_odd hEven _ p hp).2)
  have hmass : H*(∑ k ∈ occupied N e ξ ρ, F k*cellMass N e ξ ρ k) ≤
      weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ := by
    unfold weightedGridMass plainGridMass
    simp only [mul_sum]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro k hk
    simpa only [mul_assoc,add_mul] using mul_le_mul_of_nonneg_right
      (hlocal k hk) (cellMass_nonneg _ _ _ _ _)
  calc
    _ ≤ fouvryG9BaseEuler N (sqrt N)*fullEulerCorrection N*
        (∑ k ∈ occupied N e ξ ρ, F k*cellMass N e ξ ρ k) := hbound
    _ ≤ fouvryG9BaseEuler N (sqrt N)*(1+ζ)*
        (∑ k ∈ occupied N e ξ ρ, F k*cellMass N e ξ ρ k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hb0) hsum0
    _ ≤ (H*(1+ζ)*S)*(1+ζ)*
        (∑ k ∈ occupied N e ξ ρ, F k*cellMass N e ξ ρ k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrawEuler (by linarith)) hsum0
    _ = (1+ζ)^2*S*(H*(∑ k ∈ occupied N e ξ ρ, F k*cellMass N e ξ ρ k)) := by ring
    _ ≤ (1+ζ)^2*S*(weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg _) hS)
    _ = _ := by dsimp [S,E,H]

#print axioms properMain_weighted_upper
end Wu08FirstPrimeFour.Normalization
