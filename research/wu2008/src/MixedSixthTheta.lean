import MixedSixthFlatten

namespace MixedSixth
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- Exact partition identity for any weight on the literal pair carrier. -/
theorem fine_sum {N : ℕ} (hN : 1 < N) (a b c d : ℝ) (f : ℕ × ℕ → ℝ) :
    (∑ j ∈ truncatedSixthMassPacking N a b c d,
      ∑ p ∈ truncatedSixthMassPackingBox N a c j, f p) =
      ∑ p ∈ truncatedSixthClosurePairs N a (truncatedSixthMassTerminal N a b)
        c (truncatedSixthMassTerminal N c d), f p := by
  unfold truncatedSixthMassPacking truncatedSixthMassPackingBox
    truncatedSixthLowerBoxPairs truncatedSixthClosurePairs
  simp only [sum_product]
  rw [truncatedSixthMass_grid_sum hN a b]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  exact (truncatedSixthMass_grid_sum hN c d (fun q => f (p,q))).symm

/-- The high orientation uses the actual C(pqN), and dominates the entire
classical theta weight of the same box, rather than an independent count. -/
theorem theta_dominates_classical {N : ℕ} {δ Δ X Y : ℝ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hr : truncatedSixthLowerRegion δ X Y)
    (hp : (N:ℝ)^truncatedSixthLowerAlpha ≤ (N:ℝ)^X/Δ)
    (hq : (N:ℝ)^truncatedSixthLowerBeta ≤ (N:ℝ)^Y/Δ) :
    (∑ p ∈ truncatedSixthLowerBoxPairs N Δ X Y, truncatedSixthLowerClassicalTheta N δ p) ≤
      boxTheta N ((N:ℝ)^truncatedSixthLowerC δ)
        (convolutionWuWindows N Δ ![(N:ℝ)^X,(N:ℝ)^Y]) := by
  have hN1 : 1 < N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : convolutionWuWindows N Δ ![(N:ℝ)^X,(N:ℝ)^Y] =
      ![primeWindow N ((N:ℝ)^X/Δ) ((N:ℝ)^X),primeWindow N ((N:ℝ)^Y/Δ) ((N:ℝ)^Y)] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun z => Fin.elim0 z) k) j
  rw [boxTheta,hW]
  simp only [mul_div_assoc]
  rw [truncatedSixthLower_two_window_sum,mul_sum]
  apply sum_le_sum
  intro p hmem
  have hsub := HighConsumer.retained_box_subset hN1 hr hp hq hmem
  have hs := (truncatedSixthLower_prime_s_bounds hN1 hδ hsub).1
  have hz : 0 < log ((N:ℝ)^truncatedSixthLowerAlpha) := by
    rw [log_rpow hN0]
    exact mul_pos truncatedSixthLower_parameters.1 (log_pos (by exact_mod_cast hN1))
  have hl : 0 < log ((N:ℝ)^truncatedSixthLowerC δ / (p.1*p.2:ℕ)) := by
    have h := (le_div_iff₀ hz).mp hs
    linarith
  have hp0 := (mem_primeWindow.mp (mem_product.mp hmem).1).1.pos
  have hq0 := (mem_primeWindow.mp (mem_product.mp hmem).2).1.pos
  have hd0 := Nat.mul_pos hp0 hq0
  have ht0 : (0:ℝ) < Nat.totient (p.1*p.2) := by exact_mod_cast Nat.totient_pos.mpr hd0
  have hli : 0 ≤ logarithmicIntegral N :=
    (show (0:ℝ) ≤ N/(2*log N) by positivity).trans (box_trueLi_lower hN)
  have hC := wuSingularSeries_le_mul (N := N) (d := p.1*p.2) (by omega) hd0
  change 4*logarithmicIntegral N*wuSingularSeries N /
      ((Nat.totient (p.1*p.2):ℝ)*log ((N:ℝ)^truncatedSixthLowerC δ/(p.1*p.2:ℕ))) ≤ _
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hC (mul_pos ht0 hl).le) (by positivity)

def rectangleTheta (N : ℕ) (δ a b c d : ℝ) : ℝ :=
  ∑ j ∈ truncatedSixthMassPacking N a b c d,
    boxTheta N ((N:ℝ)^truncatedSixthLowerC δ)
      (convolutionWuWindows N (truncatedSixthMassDelta N)
        ![(N:ℝ)^truncatedSixthMassGridPoint N a (j.1+1),
          (N:ℝ)^truncatedSixthMassGridPoint N c (j.2+1)])

/-- Sharp denominator and full fine-grid reciprocal mass, valid on the
whole retained polygon including its high part. -/
theorem rectangle_theta_lower {N : ℕ} {δ a b c d : ℝ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hr : truncatedSixthLowerRegion δ b d) :
    (4*logarithmicIntegral N*wuSingularSeries N /
      ((truncatedSixthLowerC δ-a-c)*log N))*
      truncatedSixthMassPackingReciprocal N a b c d ≤ rectangleTheta N δ a b c d := by
  have hN1 : 1 < N := by omega
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN1.le
  have hbetween {X Y : ℝ} (hx : a ≤ X ∧ X ≤ b) (hy : c ≤ Y ∧ Y ≤ d) :
      truncatedSixthLowerRegion δ X Y :=
    ⟨ha.trans hx.1,hx.2.trans hr.2.1,hc.trans hy.1,hy.2.trans hr.2.2.2.1,
      (add_le_add hx.2 hy.2).trans hr.2.2.2.2⟩
  have hterm := hbetween
    ⟨(truncatedSixthMass_grid_terminal_bounds hN1 hab).1,
      (truncatedSixthMass_grid_terminal_bounds hN1 hab).2.1⟩
    ⟨(truncatedSixthMass_grid_terminal_bounds hN1 hcd).1,
      (truncatedSixthMass_grid_terminal_bounds hN1 hcd).2.1⟩
  have hbase := truncatedSixthClosure_classical_theta_lower (a := a) (c := c) hN hterm
  rw [← fine_sum hN1 a b c d,← fine_sum hN1 a b c d] at hbase
  apply hbase.trans
  apply sum_le_sum
  intro j hj
  obtain ⟨hj1,hj2⟩ := mem_product.mp hj
  have hx := truncatedSixthMass_grid_point_bounds hN1 hab (mem_range.mp hj1)
  have hy := truncatedSixthMass_grid_point_bounds hN1 hcd (mem_range.mp hj2)
  apply theta_dominates_classical hN hδ (hbetween
    ⟨hx.1.trans ((truncatedSixthMass_grid_point_mono hN1 a).monotone (Nat.le_succ _)),hx.2⟩
    ⟨hy.1.trans ((truncatedSixthMass_grid_point_mono hN1 c).monotone (Nat.le_succ _)),hy.2⟩)
  · rw [truncatedSixthMass_grid_lower_endpoint hN1]
    exact rpow_le_rpow_of_exponent_le hNR (ha.trans hx.1)
  · rw [truncatedSixthMass_grid_lower_endpoint hN1]
    exact rpow_le_rpow_of_exponent_le hNR (hc.trans hy.1)

end
end MixedSixth
