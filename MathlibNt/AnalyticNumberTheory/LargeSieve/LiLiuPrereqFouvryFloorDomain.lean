import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFloorCutoff
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFullLevelDomain

/-!
# Exact inner interval for the paid floor cutoff

The repaired cutoff has a closed ceiling lower endpoint involving `|h|`,
not the old strict floor endpoint involving `|h|-1`. These identities retain
the fixed gcd condition; they do not remove the other arithmetic masks.
-/

noncomputable section
open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wFloorCutoff_frequency_iff {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z)
    (q r : ℕ) (h : ℤ) :
    h.natAbs ≤ wFloorCutoff M Z q r ↔
      (h.natAbs : ℝ) ≤ (q.lcm r : ℝ) / M * Z := by
  unfold wFloorCutoff
  exact Nat.le_floor_iff (by positivity)

theorem wFloorCutoff_factor_interval_iff {M Z : ℝ} (hM : 0 < M) (hZ : 0 < Z)
    {q d k δ : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hg : q.gcd (d * k) = δ) (h : ℤ) :
    h.natAbs ≤ wFloorCutoff M Z q (d * k) ↔
      ⌈(h.natAbs : ℝ) * M * δ / ((q : ℝ) * d * Z)⌉₊ ≤ k := by
  have hδ : 0 < δ := hg ▸ Nat.gcd_pos_of_pos_left (d * k) hq
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hδr : (0 : ℝ) < δ := Nat.cast_pos.mpr hδ
  have hl : (q.lcm (d * k) : ℝ) = (q : ℝ) * d * k / δ := by
    apply (eq_div_iff hδr.ne').mpr
    have he := Nat.gcd_mul_lcm q (d * k)
    rw [hg] at he
    have he' : (δ : ℝ) * (q.lcm (d * k) : ℝ) = (q : ℝ) * (d * k) := by
      exact_mod_cast he
    nlinarith
  rw [wFloorCutoff_frequency_iff hM hZ.le, Nat.ceil_le, hl]
  rw [div_le_iff₀ (by positivity : 0 < (q : ℝ) * d * Z)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hM, div_mul_eq_mul_div, le_div_iff₀ hδr]
  constructor <;> intro he <;> nlinarith

theorem wFloorCutoff_factor_mem_Icc_iff {M Z : ℝ} (hM : 0 < M) (hZ : 0 < Z)
    {q d k δ F : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hg : q.gcd (d * k) = δ) (h : ℤ) :
    k ≤ F ∧ h.natAbs ≤ wFloorCutoff M Z q (d * k) ↔
      k ∈ Icc ⌈(h.natAbs : ℝ) * M * δ / ((q : ℝ) * d * Z)⌉₊ F := by
  rw [wFloorCutoff_factor_interval_iff hM hZ hq hd hg, mem_Icc, and_comm]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
