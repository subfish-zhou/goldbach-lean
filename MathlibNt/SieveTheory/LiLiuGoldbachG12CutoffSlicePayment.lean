import MathlibNt.SieveTheory.LiLiuGoldbachG12GridAdmission
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory

namespace G12FineGrid

/-- The original prime-output count on the retained integer cutoff slice. -/
def cutoffOutput (N : ℕ) (ε : ℝ) : ℝ :=
  400 * ∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 *
    (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)

/-- A fixed short coordinate leaves at most N/r positive long coordinates. -/
theorem cutoffSlice_card {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) :
    (cutoffSlice N ε).card ≤ N / lowCut N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : 0 < lowCut N := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hNp _)
  have hc : (cutoffSlice N ε).card ≤ (Icc 1 (N / lowCut N)).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hm,he⟩ := (cutoffSlice_iff N p.1 p.2 ε).mp hp
      have hm0 := (mother_coordinates hm).1
      have hn := (mem_filter.mp hm).2.2.2.2.2.2.1
      change p.2 * p.1 < N at hn
      rw [he] at hn
      exact mem_Icc.mpr ⟨hm0,(Nat.le_div_iff_mul_le hr).mpr (by simpa only [Nat.mul_comm] using hn.le)⟩
    · intro p hp q hq he
      apply Prod.ext he
      exact ((cutoffSlice_iff N p.1 p.2 ε).mp hp).2.trans
        ((cutoffSlice_iff N q.1 q.2 ε).mp hq).2.symm
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc

/-- Dropping the output primality test is an inequality, not deletion of the slice. -/
theorem cutoffOutput_le {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) :
    cutoffOutput N ε ≤ 400 * (N : ℝ) / lowCut N := by
  have hw : (∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 *
      (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤ (cutoffSlice N ε).card := by
    calc
      _ ≤ ∑ _p ∈ cutoffSlice N ε, (1 : ℝ) := by
        apply sum_le_sum
        intro p _
        split_ifs
        · simpa only [mul_one] using (goldbachG12NormalizedCoefficient_bounds N p.1).2
        · norm_num
      _ = _ := by simp
  have hc : ((cutoffSlice N ε).card : ℝ) ≤ N / (lowCut N : ℝ) :=
    (show ((cutoffSlice N ε).card : ℝ) ≤ (N / lowCut N : ℕ) by
      exact_mod_cast cutoffSlice_card hN ε).trans Nat.cast_div_le
  unfold cutoffOutput
  calc
    _ ≤ (400 : ℝ) * (cutoffSlice N ε).card := mul_le_mul_of_nonneg_left hw (by norm_num)
    _ ≤ 400 * ((N : ℝ) / lowCut N) := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring

/-- The rounded cutoff is paid by its exact positive-power lower bound. -/
theorem cutoffOutput_power {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) :
    cutoffOutput N ε ≤ 400 * (N : ℝ) / (N : ℝ)^(4/53 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (cutoffOutput_le hN ε).trans
    (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNp _)
      (Nat.le_ceil _))

/-- Arbitrary real logarithmic saving, uniformly in the original prefix. -/
theorem cutoffOutput_log_saving (B : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ,
      cutoffOutput N ε ≤ N / Real.log (N : ℝ)^B := by
  obtain ⟨N₀,hN₀,h⟩ := G12RectangleGate.numerical_log_saving B
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ε
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hs : (1 : ℝ) ≤ (1+Real.log (N : ℝ))^2 := by nlinarith
  have hz : 0 ≤ (N : ℝ) / (N : ℝ)^(4/53 : ℝ) := by positivity
  calc
    _ ≤ 400 * (N : ℝ) / (N : ℝ)^(4/53 : ℝ) := cutoffOutput_power (by omega) ε
    _ ≤ (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 := by
      have hh := mul_le_mul_of_nonneg_left hs hz
      simp only [mul_div_assoc] at *
      nlinarith
    _ ≤ _ := h N hN

/-- The physical coefficient 400 and actual singular series both remain present. -/
theorem cutoffOutput_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ,
      cutoffOutput N ε ≤
        δ * (SingularSeries.liuSingularSeries N * N / Real.log (N : ℝ)^2) := by
  obtain ⟨A,hA,ha⟩ := cutoffOutput_log_saving 3
  obtain ⟨B,hb⟩ := eventually_atTop.mp (goldbachBV_logCube_normalized 1 δ hδ)
  refine ⟨max A B,by omega,?_⟩
  intro N hN ε
  have h := ha N (by omega) ε
  have h' := hb N (by omega)
  simp only [Real.rpow_ofNat] at h
  simp only [one_mul] at h'
  exact h.trans h'

end G12FineGrid
