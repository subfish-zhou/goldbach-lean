import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaDifferentialTail

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000


/-- Bound the moving perturbation slope by its logarithmic majorant. -/
lemma moving_perturbationSlope_le_log
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d) (ht : 0 < t) :
    perturbationSlope D d 0 t ≤
      (d + 1) * Real.log (1 + t ^ d / Real.log D) := by
  let z : ℝ := t ^ d / Real.log D
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
  have hb : 0 < 1 + z := by linarith
  have hzlog : z / (1 + z) ≤ Real.log (1 + z) := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [Real.log_inv] at hi
    have heq : z / (1 + z) = 1 - (1 + z)⁻¹ := by
      field_simp [hb.ne']
      ring
    rw [heq]
    linarith
  have htpow : t * t ^ (d - 1) = t ^ d := by
    calc
      t * t ^ (d - 1) = t ^ (1 : ℝ) * t ^ (d - 1) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (d - 1)) := (Real.rpow_add ht _ _).symm
      _ = t ^ d := by ring_nf
  have hterm : t * (d * t ^ (d - 1) / Real.log D) /
        (1 + t ^ d / Real.log D) = d * (z / (1 + z)) := by
    dsimp [z]
    rw [show t * (d * t ^ (d - 1) / Real.log D) =
      d * (t * t ^ (d - 1)) / Real.log D by ring, htpow]
    ring
  rw [perturbationSlope]
  simp only [add_zero]
  rw [hterm]
  calc
    Real.log (1 + z) + d * (z / (1 + z)) ≤
        Real.log (1 + z) + d * Real.log (1 + z) := by gcongr
    _ = (d + 1) * Real.log (1 + z) := by ring

/-- Below the moving cutoff, the normalized real power is at most one. -/
lemma moving_below_cutoff_z_le_one
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d) (ht : 0 < t)
    (hcut : t ≤ (Real.log D) ^ (1 / d)) :
    t ^ d / Real.log D ≤ 1 := by
  have hp := Real.rpow_le_rpow ht.le hcut hd.le
  have hc : ((Real.log D) ^ (1 / d)) ^ d = Real.log D := by
    simpa only [one_div] using Real.rpow_inv_rpow hlog.le hd.ne'
  rw [hc] at hp
  exact (div_le_one hlog).2 hp

/-- Above the moving cutoff, the normalized real power is strictly greater than one. -/
lemma moving_above_cutoff_one_lt_z
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (hcut : (Real.log D) ^ (1 / d) < t) :
    1 < t ^ d / Real.log D := by
  have hp := Real.rpow_lt_rpow (Real.rpow_nonneg hlog.le _) hcut hd
  have hc : ((Real.log D) ^ (1 / d)) ^ d = Real.log D := by
    simpa only [one_div] using Real.rpow_inv_rpow hlog.le hd.ne'
  rw [hc] at hp
  exact (one_lt_div hlog).2 hp


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
