import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePairingConservation

/-!
# Tail of the upper-source pairing window

The unit-window term tends to zero from the genuine source tail and the scaled
Laplace tail of the standard upper adjoint.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

/-- The moving-window term in the upper-source pairing tends to zero once the
source tends to `2`; the standard-adjoint scaled tail is supplied by its actual
Laplace-integral producer. -/
theorem suzukiUpperSourcePairingWindowTail_of_sourceTail
    (hP : SuzukiUpperSourcePTail) :
    SuzukiUpperSourcePairingWindowTail := by
  unfold SuzukiUpperSourcePTail at hP
  have hp : SuzukiStandardUpperAdjointScaledTail :=
    suzukiStandardUpperAdjoint_scaledTail
  unfold SuzukiStandardUpperAdjointScaledTail at hp
  unfold SuzukiUpperSourcePairingWindowTail
  rw [Metric.tendsto_atTop] at hP hp ⊢
  intro ε hε
  obtain ⟨NP, hNP⟩ := hP 1 zero_lt_one
  obtain ⟨Np, hNp⟩ := hp 1 zero_lt_one
  refine ⟨max (max (NP + 1) Np) (max 2 (7 / ε)), ?_⟩
  intro s hs
  have hsNP : NP + 1 ≤ s :=
    le_trans (le_max_left (NP + 1) Np) (le_trans (le_max_left _ _) hs)
  have hsNp : Np ≤ s :=
    le_trans (le_max_right (NP + 1) Np) (le_trans (le_max_left _ _) hs)
  have hs2 : 2 ≤ s :=
    le_trans (le_max_left 2 (7 / ε)) (le_trans (le_max_right _ _) hs)
  have hspos : 0 < s := by linarith
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  apply lt_of_le_of_lt
    (intervalIntegral.norm_integral_le_of_norm_le_const (C := 6 / s) ?_)
  · rw [show |s - (s - 1)| = 1 by
      rw [show s - (s - 1) = 1 by ring]
      norm_num, mul_one]
    have heps : 6 / s ≤ 6 / (7 / ε) := by
      gcongr
      exact le_trans (le_max_right 2 (7 / ε)) (le_trans (le_max_right _ _) hs)
    have hcalc : 6 / (7 / ε) < ε := by
      field_simp
      nlinarith
    exact heps.trans_lt hcalc
  · intro t ht
    rw [uIoc_of_le (by linarith : s - 1 ≤ s)] at ht
    have htS : s ≤ t + 1 := by linarith [ht.1]
    have htNP : NP ≤ t := by linarith [hsNP, ht.1]
    have htNp : Np ≤ t + 1 := hsNp.trans htS
    have hPb := hNP t htNP
    have hpb := hNp (t + 1) htNp
    rw [Real.dist_eq] at hPb hpb
    have hPnorm : ‖suzukiUpperSourceP t‖ ≤ 3 := by
      rw [Real.norm_eq_abs]
      have : |suzukiUpperSourceP t| < 3 := by
        rw [abs_sub_lt_iff] at hPb
        rw [abs_lt]
        constructor <;> linarith [hPb.1, hPb.2]
      exact this.le
    have hqnorm : ‖(t + 1) * suzukiStandardUpperAdjoint (t + 1)‖ ≤ 2 := by
      rw [Real.norm_eq_abs]
      have : |(t + 1) * suzukiStandardUpperAdjoint (t + 1)| < 2 := by
        rw [abs_sub_lt_iff] at hpb
        rw [abs_lt]
        constructor <;> linarith [hpb.1, hpb.2]
      exact this.le
    have htpos : 0 < t + 1 := hspos.trans_le htS
    rw [show suzukiStandardUpperAdjoint (t + 1) =
        ((t + 1) * suzukiStandardUpperAdjoint (t + 1)) / (t + 1) by
          field_simp]
    rw [norm_mul, norm_div]
    simp only [Real.norm_eq_abs, abs_of_pos htpos]
    calc
      ‖(t + 1) * suzukiStandardUpperAdjoint (t + 1)‖ /
            (t + 1) * ‖suzukiUpperSourceP t‖
          ≤ 2 / (t + 1) * 3 := by gcongr
      _ ≤ 2 / s * 3 := by gcongr
      _ = 6 / s := by ring


end
end MathlibNt.SieveTheory
