import FifthHCell
import MathlibNt.Wu2008DoubleSieve.FifthPairCell

namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology

/-- F5 has its own legal depth-two source geometry, not the F6 region. -/
theorem fifthH_mesh_source {N : ℕ} {δ x y : ℝ}
    (hN : 1 < N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000)
    (hx : truncatedSixthLowerAlpha ≤ x) (hxy : x ≤ y)
    (hy : y ≤ truncatedSixthLowerBeta) :
    wuSourceBox 2 δ N 2 (truncatedSixthMassDelta N)
      ![(N : ℝ) ^ y, (N : ℝ) ^ x] := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hg := fifthPair_triangle_bounds hδ.le hδhi hx hxy hy
  have hd := truncatedSixthLower_depth_two hδ (by linarith)
  have hD := truncatedSixthMass_delta_legal hN
  refine ⟨le_rfl, hD.2.1, hD.2.2, ?_, ?_, ?_⟩
  · intro j k hjk
    have hj : j = 0 ∨ j = 1 := by omega
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
    · exact le_rfl
    · exact rpow_le_rpow_of_exponent_le hNR hxy
    · simp at hjk
    · exact le_rfl
  · intro j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · exact rpow_le_rpow_of_exponent_le hNR (hd.le.trans (hx.trans hxy))
    · exact rpow_le_rpow_of_exponent_le hNR (hd.le.trans hx)
  · intro j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · norm_num [Finset.prod_filter, Fin.prod_univ_two]
      change ((N : ℝ) ^ y) ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ)
      rw [← rpow_natCast, ← rpow_mul hN0.le]
      apply rpow_le_rpow_of_exponent_le hNR
      change y * 2 ≤ truncatedSixthLowerC δ
      linarith [hg.2.2.2.2.1, hg.2.2.2.2.2]
    · norm_num [Finset.prod_filter, Fin.prod_univ_two]
      change (N : ℝ) ^ y * ((N : ℝ) ^ x) ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ)
      rw [← rpow_natCast, ← rpow_mul hN0.le, ← rpow_add hN0]
      apply rpow_le_rpow_of_exponent_le hNR
      change y + x * 2 ≤ truncatedSixthLowerC δ
      linarith [hg.2.2.2.2.1, hg.2.2.2.2.2]

/-- The old packing is an exact half-open partition of the trimmed rectangle. -/
theorem fifthH_mesh_sum {N : ℕ} (hN : 1 < N) (a b c d : ℝ) (f : ℕ × ℕ → ℝ) :
    (∑ j ∈ truncatedSixthMassPacking N a b c d,
      ∑ p ∈ truncatedSixthMassPackingBox N a c j, f p) =
    ∑ p ∈ truncatedSixthClosurePairs N a (truncatedSixthMassTerminal N a b)
      c (truncatedSixthMassTerminal N c d), f p := by
  unfold truncatedSixthMassPacking truncatedSixthMassPackingBox truncatedSixthLowerBoxPairs
    truncatedSixthClosurePairs
  simp only [sum_product]
  rw [truncatedSixthMass_grid_sum hN a b]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [truncatedSixthMass_grid_sum hN c d]

/-- The geometric packing never escapes its original exponent cell. -/
theorem fifthH_mesh_subset {N : ℕ} {a b c d : ℝ}
    (hN : 1 < N) (hab : a ≤ b) (hcd : c ≤ d) :
    truncatedSixthClosurePairs N a (truncatedSixthMassTerminal N a b)
      c (truncatedSixthMassTerminal N c d) ⊆ truncatedSixthClosurePairs N a b c d := by
  intro p hp
  obtain ⟨hp, hq⟩ := mem_product.mp hp
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  exact mem_product.mpr ⟨mem_primeWindow.mpr ⟨hp'.1, hp'.2.1, hp'.2.2.1,
    hp'.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR
      (truncatedSixthMass_grid_terminal_bounds hN hab).2.1)⟩,
    mem_primeWindow.mpr ⟨hq'.1, hq'.2.1, hq'.2.2.1,
    hq'.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR
      (truncatedSixthMass_grid_terminal_bounds hN hcd).2.1)⟩⟩

/-- No source-box or covering hypothesis: only original rectangle geometry.
The single fixed s and its raw threshold precede the entire moving packing. -/
theorem fifthH_mesh_raw {δ s η a b c d : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hd : d ≤ truncatedSixthLowerBeta)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) (hsCell : s ≤ truncatedSixthLowerS δ b d) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (wuLowerCoefficient s + (wuImprovementLimit false δ s - η)) *
        truncatedSixthMassPackingTheta N δ a b c d ≤
      truncatedSixthClosureCount N a b c d := by
  obtain ⟨T, hT4, hraw⟩ := fifthH_original_cell_raw hδ (by linarith) hs hs10 hη
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  have hN1 : 1 < N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsum : (wuLowerCoefficient s + (wuImprovementLimit false δ s - η)) *
      truncatedSixthMassPackingTheta N δ a b c d ≤
      ∑ j ∈ truncatedSixthMassPacking N a b c d,
        ∑ p ∈ truncatedSixthMassPackingBox N a c j,
          (sieveCount N (p.1 * p.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
    unfold truncatedSixthMassPackingTheta
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_product.mp hj
    have hx := truncatedSixthMass_grid_point_bounds hN1 hab (mem_range.mp hj1)
    have hy := truncatedSixthMass_grid_point_bounds hN1 hcd (mem_range.mp hj2)
    have hxm := (truncatedSixthMass_grid_point_mono hN1 a).monotone (Nat.le_succ j.1)
    have hym := (truncatedSixthMass_grid_point_mono hN1 c).monotone (Nat.le_succ j.2)
    have hxy := hx.2.trans (hbc.trans (hy.1.trans hym))
    have hb := fifthH_mesh_source hN1 hδ hδhi (ha.trans (hx.1.trans hxm)) hxy (hy.2.trans hd)
    have hz : ∀ k : Fin 2, (N : ℝ) ^ truncatedSixthLowerAlpha ≤
        (![(N : ℝ) ^ truncatedSixthMassGridPoint N c (j.2 + 1),
          (N : ℝ) ^ truncatedSixthMassGridPoint N a (j.1 + 1)] k) / truncatedSixthMassDelta N := by
      intro k
      have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl
      · simp only [Matrix.cons_val_zero]
        rw [truncatedSixthMass_grid_lower_endpoint hN1]
        exact rpow_le_rpow_of_exponent_le hNR (ha.trans (hab.trans (hbc.trans hy.1)))
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [truncatedSixthMass_grid_lower_endpoint hN1]
        exact rpow_le_rpow_of_exponent_le hNR (ha.trans hx.1)
    have hsep : (N : ℝ) ^ truncatedSixthMassGridPoint N a (j.1 + 1) ≤
        (N : ℝ) ^ truncatedSixthMassGridPoint N c (j.2 + 1) / truncatedSixthMassDelta N := by
      rw [truncatedSixthMass_grid_lower_endpoint hN1]
      exact rpow_le_rpow_of_exponent_le hNR (hx.2.trans (hbc.trans hy.1))
    have hbudget : ((N : ℝ) ^ truncatedSixthLowerAlpha) ^ s *
        ((N : ℝ) ^ truncatedSixthMassGridPoint N c (j.2 + 1) *
          (N : ℝ) ^ truncatedSixthMassGridPoint N a (j.1 + 1)) ≤
        (N : ℝ) ^ (1 / 2 - δ) := by
      rw [← rpow_mul hN0.le, ← rpow_add hN0, ← rpow_add hN0]
      apply rpow_le_rpow_of_exponent_le hNR
      have h := (le_div_iff₀ truncatedSixthLower_parameters.1).mp hsCell
      change _ ≤ truncatedSixthLowerC δ
      linarith
    exact (hraw N hN he _ _ hb hz hsep
      (rpow_le_rpow_of_exponent_le hNR (hy.2.trans hd)) hbudget).2
  rw [fifthH_mesh_sum hN1] at hsum
  apply hsum.trans
  apply sum_le_sum_of_subset_of_nonneg (fifthH_mesh_subset hN1 hab hcd)
  intro p _ _
  unfold sieveCount
  positivity
end Wu2008DoubleSieve
