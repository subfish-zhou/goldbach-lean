import Wu08SmallGridTransport

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.SmallGrid
open Normalization

/-- Consumes the already closed actual properMain epsilon normalization.
One N threshold precedes every legal grid; no new mass estimate is assumed.
The remaining target is the explicit relaxed labelled rough sum. -/
theorem properMain_relaxed {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
    ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
      properMain N e ξ ρ δ η ≤
        (wuSingularSeries N/log N)*relaxedMass N e ρ ε := by
  obtain ⟨δ,η,hδ,hδu,hη,hηu,T,hT⟩ := properMain_epsilon_normalized hε
  obtain ⟨Tb,hb⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 8 0 truncatedSixthLowerAlpha
      (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨δ,η,hδ,hδu,hη,hηu,max 4 (max T Tb),?_⟩
  intro N hN hEven e ξ ρ hξ hρ hρu
  have hn4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNTb : Tb ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlarge : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2 := by
    have hh : (8 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hNTb
    linarith
  have hs : 0 ≤ wuSingularSeries N/log N := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (log_nonneg (by linarith))
  exact (hT N hNT hEven e ξ ρ hξ hρ hρu).trans
    (mul_le_mul_of_nonneg_left (gridMass_le_relaxed hn4 hξ hρ hρu hlarge hε.le) hs)

#print axioms properMain_relaxed
end Wu08FirstPrimeFour.SmallGrid
