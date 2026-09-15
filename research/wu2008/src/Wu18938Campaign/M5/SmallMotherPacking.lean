import Wu18938Campaign.M5.SmallMotherDifference
import Wu18938Campaign.M5.LiteralIdentity

noncomputable section

namespace Wu18938Campaign.M5.SmallMotherPacking

open Real Finset Wu2008DoubleSieve WuPaper.R2SixthCount
open SmallMotherDifference
open scoped Classical

def motherMass (N : ℕ) (δ Δ l u : ℝ) : ℝ :=
  ∑ j ∈ range (gamma5GainSize N Δ l u),
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
      (convolutionWuWindows N Δ (fun _ : Fin 1 => gamma5GainEnd N Δ l j))

theorem rectangle_grid_sum {N : ℕ} {Δ l u v w : ℝ}
    (hN : 2 ≤ N) (hΔ : 1 < Δ) :
    (rectangleCount N l (gamma5GainTerminal N Δ l u) v w : ℝ) =
      ∑ j ∈ range (gamma5GainSize N Δ l u),
        (rectangleCount N (gamma5GainPoint N Δ l j)
          (gamma5GainPoint N Δ l (j + 1)) v w : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  simp only [rectangleCount, Int.cast_sum, window]
  simp_rw [gamma5Gain_grid_sum hNr hΔ]
  rw [sum_comm]
  simp_rw [gamma5Gain_end_lower hNr hΔ]
  rfl

/-- A fixed threshold covers the entire existing prime microgrid, even as its size grows. -/
theorem rectangle_lower {δ l u v w s t ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hl : alpha ≤ l) (hlu : l ≤ u) (hv : alpha ≤ v)
    (hu : u ≤ (1 / 2 - δ) / 2)
    (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10)
    (hvt : v * t ≤ (1 / 2 - δ) - u)
    (hws : (1 / 2 - δ) - l ≤ w * s) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        (endpointCoefficient δ s t - ε) * motherMass N δ Δ l u ≤
          (rectangleCount N l u v w : ℝ) := by
  obtain ⟨T, hT4, hT⟩ := rectangle_cell_lower hδ hδhi hl hv hu hs hst ht10 hvt hws hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he Δ hΔlo hΔhi
  have hN4 := hT4.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hΔ : 1 < Δ := by
    have hp := rpow_pos_of_pos (log_pos hNr) (-4 : ℝ)
    linarith
  have hm := (gamma5Gain_point_strictMono hNr hΔ l).monotone
  have hc :
      (endpointCoefficient δ s t - ε) * motherMass N δ Δ l u ≤
        (rectangleCount N l (gamma5GainTerminal N Δ l u) v w : ℝ) := by
    rw [rectangle_grid_sum (by omega) hΔ, motherMass, mul_sum]
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    have hg := gamma5Gain_point_bounds hNr hΔ hlu hj'
    exact hT N hN he Δ hΔlo hΔhi _ _ hg.1 (hm (by omega)) hg.2
      (gamma5Gain_end_lower hNr hΔ l j)
  have hmono := LiteralCount.pairCount_first_upper_mono (v := v) (w := w) (l := l)
    (show 1 ≤ N by omega) (gamma5Gain_terminal_bounds hNr hΔ hlu).2.1
  rw [LiteralIdentity.pairCount_eq, LiteralIdentity.pairCount_eq] at hmono
  exact hc.trans (by exact_mod_cast hmono)

set_option pp.universes true
set_option pp.fullNames true

#check @motherMass
#print axioms motherMass
#check @rectangle_grid_sum
#print axioms rectangle_grid_sum
#check @rectangle_lower
#print axioms rectangle_lower

end Wu18938Campaign.M5.SmallMotherPacking
