import MathlibNt.Wu2008DoubleSieve.SeventhEighthFixedGeometry
import MathlibNt.Wu2008DoubleSieve.NinthMainMassQuadrature

/-! Literal logarithmic geometry of the physical labelled domains.
Strict finite faces are preserved, not removed by measure-zero arguments. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Real Set Finset

/-- This statement uses only actual ordered prime-pair geometry. -/
theorem classical_pair_log_geometry {N a b : ℕ} {s u : ℝ}
    (hN : 1 < N) (ha : a.Prime) (hb : b.Prime) (hab : a < b)
    (hsa : (N : ℝ) ^ s ≤ a) (hub : (N : ℝ) ^ u ≤ b)
    (hsize : a * b ^ 2 < N) :
    s ≤ ninthMainCoordinate N a ∧ u ≤ ninthMainCoordinate N b ∧
      ninthMainCoordinate N a < ninthMainCoordinate N b ∧
      ninthMainCoordinate N a + 2 * ninthMainCoordinate N b < 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.pos
  have hlo := log_le_log (rpow_pos_of_pos hN0 s) hsa
  have hu := log_le_log (rpow_pos_of_pos hN0 u) hub
  rw [log_rpow hN0] at hlo hu
  have horder := log_lt_log ha0 (show (a : ℝ) < b by exact_mod_cast hab)
  have hs : (a : ℝ) * (b : ℝ) ^ (2 : ℕ) < N := by exact_mod_cast hsize
  have hlogs := log_lt_log (mul_pos ha0 (sq_pos_of_pos hb0)) hs
  rw [log_mul ha0.ne' (sq_pos_of_pos hb0).ne', log_pow] at hlogs
  norm_num only [Nat.cast_ofNat] at hlogs
  refine ⟨(le_div_iff₀ hL).mpr hlo, (le_div_iff₀ hL).mpr hu,
    (div_lt_div_iff_of_pos_right hL).mpr horder, ?_⟩
  unfold ninthMainCoordinate
  rw [← mul_div_assoc, ← add_div, div_lt_iff₀ hL, one_mul]
  exact hlogs

theorem seventh_pair_log_domain {N : ℕ} (hN : 1 < N) {a b : ℕ}
    (hp : (a, b) ∈ seventhPairs N) :
    sigma ≤ ninthMainCoordinate N a ∧ ninthMainCoordinate N a < 1 / 3 ∧
      ninthMainCoordinate N a < ninthMainCoordinate N b ∧
      ninthMainCoordinate N b < (1 - ninthMainCoordinate N a) / 2 := by
  obtain ⟨hm, hu⟩ := mem_filter.mp hp
  obtain ⟨ha, hb, _, _, _, hub, hab, hs⟩ := lowerPairs_data hm
  obtain ⟨hlo, _, hab', hs'⟩ := classical_pair_log_geometry hN ha hb hab hu hub hs
  exact ⟨hlo, by linarith, hab', by linarith⟩

theorem eighth_pair_log_domain {N : ℕ} (hN : 1 < N) {a b : ℕ}
    (hp : (a, b) ∈ eighthPairs N) :
    alpha ≤ ninthMainCoordinate N a ∧ ninthMainCoordinate N a < 1 / 3 ∧
      (1 / 3 : ℝ) ≤ ninthMainCoordinate N b ∧
      ninthMainCoordinate N b < (1 - ninthMainCoordinate N a) / 2 := by
  obtain ⟨hm, _⟩ := mem_filter.mp hp
  obtain ⟨ha, hb, _, _, hza, hvb, hab, hs⟩ := lowerPairs_data hm
  obtain ⟨hlo, hv, hab', hs'⟩ := classical_pair_log_geometry hN ha hb hab hza hvb hs
  exact ⟨hlo, by linarith, hv, by linarith⟩

/-- The original physical carrier supplies the exact triangle. -/
theorem physicalT7_log_domain {N a b r : ℕ} (hN : 1 < N)
    (hp : (⟨(a, b), r⟩ : NinthLabel) ∈ physicalT7 N) :
    sigma ≤ ninthMainCoordinate N a ∧ ninthMainCoordinate N a < 1 / 3 ∧
      ninthMainCoordinate N a < ninthMainCoordinate N b ∧
      ninthMainCoordinate N b < (1 - ninthMainCoordinate N a) / 2 := by
  obtain ⟨hm, hu, _⟩ := mem_physicalT7.mp hp
  exact seventh_pair_log_domain hN (mem_filter.mpr ⟨hm, hu⟩)

theorem physicalT8_log_domain {N a b r : ℕ} (hN : 1 < N)
    (hp : (⟨(a, b), r⟩ : NinthLabel) ∈ physicalT8 N) :
    alpha ≤ ninthMainCoordinate N a ∧ ninthMainCoordinate N a < 1 / 3 ∧
      (1 / 3 : ℝ) ≤ ninthMainCoordinate N b ∧
      ninthMainCoordinate N b < (1 - ninthMainCoordinate N a) / 2 := by
  obtain ⟨hm, hv, _⟩ := mem_physicalT8.mp hp
  exact eighth_pair_log_domain hN (mem_filter.mpr ⟨hm, hv⟩)

end Wu2008DoubleSieve.SeventhEighth
