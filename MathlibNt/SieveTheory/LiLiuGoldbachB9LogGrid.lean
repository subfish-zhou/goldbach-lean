import MathlibNt.SieveTheory.LiLiuGoldbachB9LogKernel
import MathlibNt.SieveTheory.LiuPrimePairLogGrid

open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Filter Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

noncomputable local instance instDecidablePropB9LogGrid (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def goldbachB9AlphaGridWidth : ℝ := 17 / 60
noncomputable def goldbachB9BetaGridWidth : ℝ := 1 / 4

noncomputable def goldbachB9AlphaGridPoint (n i : ℕ) : ℝ :=
  1 / 20 + (i : ℝ) / (n : ℝ) * goldbachB9AlphaGridWidth

noncomputable def goldbachB9BetaGridPoint (n j : ℕ) : ℝ :=
  1 / 4 + (j : ℝ) / (n : ℝ) * goldbachB9BetaGridWidth

noncomputable def goldbachB9AlphaGridStep (n : ℕ) : ℝ := goldbachB9AlphaGridWidth / n
noncomputable def goldbachB9BetaGridStep (n : ℕ) : ℝ := goldbachB9BetaGridWidth / n

noncomputable def goldbachB9LogGridCells (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q =>
    (4 / 53 : ℝ) ≤ goldbachB9AlphaGridPoint n (q.1 + 1) ∧
      (1 / 3 : ℝ) ≤ goldbachB9BetaGridPoint n (q.2 + 1) ∧
      goldbachB9AlphaGridPoint n q.1 + 2 * goldbachB9BetaGridPoint n q.2 < 1

noncomputable def goldbachB9LogGridMajorant (n N : ℕ) : ℝ :=
  ∑ q ∈ goldbachB9LogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      primeReciprocalLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))

noncomputable def goldbachB9LogGridUpperSum (n : ℕ) : ℝ :=
  ∑ q ∈ goldbachB9LogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      logarithmicRectangleMass
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))

theorem goldbachB9LogGridMajorant_eq_primeReciprocalProducts (n N : ℕ) :
    goldbachB9LogGridMajorant n N =
      ∑ q ∈ goldbachB9LogGridCells n,
        (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
          goldbachB9BetaGridPoint n (q.2 + 1))) *
          (PrimeReciprocalLogScale.primeReciprocalLogInterval N
            (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1)) *
          PrimeReciprocalLogScale.primeReciprocalLogInterval N
            (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))) := by
  simp only [goldbachB9LogGridMajorant, primeReciprocalLogRectangle_eq_mul]

theorem mem_goldbachB9LogGridCells_iff {n : ℕ} {q : Fin n × Fin n} :
    q ∈ goldbachB9LogGridCells n ↔
      (4 / 53 : ℝ) ≤ goldbachB9AlphaGridPoint n (q.1 + 1) ∧
        (1 / 3 : ℝ) ≤ goldbachB9BetaGridPoint n (q.2 + 1) ∧
        goldbachB9AlphaGridPoint n q.1 + 2 * goldbachB9BetaGridPoint n q.2 < 1 := by
  simp only [goldbachB9LogGridCells, Finset.mem_filter, Finset.mem_univ, true_and]

theorem goldbachB9AlphaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < goldbachB9AlphaGridStep n := by
  unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
  positivity

theorem goldbachB9BetaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < goldbachB9BetaGridStep n := by
  unfold goldbachB9BetaGridStep goldbachB9BetaGridWidth
  positivity

theorem goldbachB9AlphaGridPoint_eq_step (n i : ℕ) :
    goldbachB9AlphaGridPoint n i = 1 / 20 + (i : ℝ) * goldbachB9AlphaGridStep n := by
  unfold goldbachB9AlphaGridPoint goldbachB9AlphaGridStep
  ring

theorem goldbachB9BetaGridPoint_eq_step (n i : ℕ) :
    goldbachB9BetaGridPoint n i = 1 / 4 + (i : ℝ) * goldbachB9BetaGridStep n := by
  unfold goldbachB9BetaGridPoint goldbachB9BetaGridStep
  ring

theorem goldbachB9AlphaGridPoint_succ (n i : ℕ) :
    goldbachB9AlphaGridPoint n (i + 1) =
      goldbachB9AlphaGridPoint n i + goldbachB9AlphaGridStep n := by
  rw [goldbachB9AlphaGridPoint_eq_step, goldbachB9AlphaGridPoint_eq_step]
  push_cast
  ring

theorem goldbachB9BetaGridPoint_succ (n i : ℕ) :
    goldbachB9BetaGridPoint n (i + 1) =
      goldbachB9BetaGridPoint n i + goldbachB9BetaGridStep n := by
  rw [goldbachB9BetaGridPoint_eq_step, goldbachB9BetaGridPoint_eq_step]
  push_cast
  ring

theorem goldbachB9AlphaGridPoint_pos (n i : ℕ) :
    0 < goldbachB9AlphaGridPoint n i := by
  unfold goldbachB9AlphaGridPoint goldbachB9AlphaGridWidth
  positivity

theorem goldbachB9BetaGridPoint_pos (n i : ℕ) :
    0 < goldbachB9BetaGridPoint n i := by
  unfold goldbachB9BetaGridPoint goldbachB9BetaGridWidth
  positivity

theorem goldbachB9AlphaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB9AlphaGridPoint n i < goldbachB9AlphaGridPoint n (i + 1) := by
  rw [goldbachB9AlphaGridPoint_succ]
  exact lt_add_of_pos_right _ (goldbachB9AlphaGridStep_pos hn)

theorem goldbachB9BetaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB9BetaGridPoint n i < goldbachB9BetaGridPoint n (i + 1) := by
  rw [goldbachB9BetaGridPoint_succ]
  exact lt_add_of_pos_right _ (goldbachB9BetaGridStep_pos hn)

theorem goldbachB9AlphaGridPoint_mono {n i j : ℕ} (hn : 0 < n) (hij : i ≤ j) :
    goldbachB9AlphaGridPoint n i ≤ goldbachB9AlphaGridPoint n j := by
  rw [goldbachB9AlphaGridPoint_eq_step, goldbachB9AlphaGridPoint_eq_step]
  have h := mul_le_mul_of_nonneg_right
    (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) (goldbachB9AlphaGridStep_pos hn).le
  linarith

theorem goldbachB9BetaGridPoint_mono {n i j : ℕ} (hn : 0 < n) (hij : i ≤ j) :
    goldbachB9BetaGridPoint n i ≤ goldbachB9BetaGridPoint n j := by
  rw [goldbachB9BetaGridPoint_eq_step, goldbachB9BetaGridPoint_eq_step]
  have h := mul_le_mul_of_nonneg_right
    (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) (goldbachB9BetaGridStep_pos hn).le
  linarith

theorem goldbachB9AlphaGridPoint_end {n : ℕ} (hn : 0 < n) :
    goldbachB9AlphaGridPoint n n = (1 / 3 : ℝ) := by
  unfold goldbachB9AlphaGridPoint goldbachB9AlphaGridWidth
  rw [div_self (Nat.cast_ne_zero.mpr hn.ne')]
  norm_num

theorem goldbachB9BetaGridPoint_end {n : ℕ} (hn : 0 < n) :
    goldbachB9BetaGridPoint n n = (1 / 2 : ℝ) := by
  unfold goldbachB9BetaGridPoint goldbachB9BetaGridWidth
  rw [div_self (Nat.cast_ne_zero.mpr hn.ne')]
  norm_num

theorem goldbachB9AlphaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    goldbachB9AlphaGridPoint n (i + 1) ≤ (1 / 3 : ℝ) := by
  rw [← goldbachB9AlphaGridPoint_end hn]
  exact goldbachB9AlphaGridPoint_mono hn (Nat.succ_le_iff.mpr hi)

theorem goldbachB9BetaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    goldbachB9BetaGridPoint n (i + 1) ≤ (1 / 2 : ℝ) := by
  rw [← goldbachB9BetaGridPoint_end hn]
  exact goldbachB9BetaGridPoint_mono hn (Nat.succ_le_iff.mpr hi)

theorem goldbachB9LogGridCell_cornerGap_ge {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    (1 / 6 : ℝ) ≤ 1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1) := by
  have ha := goldbachB9AlphaGridPoint_succ_le_end hn q.1.isLt
  have hb := goldbachB9BetaGridPoint_succ_le_end hn q.2.isLt
  linarith

theorem goldbachB9LogGridCell_cornerGap_pos {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    0 < 1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1) :=
  lt_of_lt_of_le (by norm_num) (goldbachB9LogGridCell_cornerGap_ge hn q)

theorem goldbachB9LogGridCell_upperCorner_lt_one
    {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    goldbachB9AlphaGridPoint n (q.1 + 1) +
      goldbachB9BetaGridPoint n (q.2 + 1) < 1 := by
  linarith [goldbachB9LogGridCell_cornerGap_pos hn q]

/-- The larger ambient box retains all three closed source boundaries. -/
theorem goldbachB9Pairs_covered_by_logGrid
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ q ∈ goldbachB9LogGridCells n,
      LiuPairInLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) rs := by
  obtain ⟨hlow, hfirst, hsecond, htriangle⟩ := goldbachB9Pair_logGeometry hN hrs
  have halow : (1 / 20 : ℝ) < primeLogExponent N rs.1 := by linarith
  have hblow : (1 / 4 : ℝ) < primeLogExponent N rs.2 := by linarith
  have haup : primeLogExponent N rs.1 ≤
      1 / 20 + (n : ℝ) * goldbachB9AlphaGridStep n := by
    rw [← goldbachB9AlphaGridPoint_eq_step, goldbachB9AlphaGridPoint_end hn]
    exact hfirst
  have hbup : primeLogExponent N rs.2 ≤
      1 / 4 + (n : ℝ) * goldbachB9BetaGridStep n := by
    rw [← goldbachB9BetaGridPoint_eq_step, goldbachB9BetaGridPoint_end hn]
    exact goldbachB9PrimeLogExponent_second_le_upper hN hrs
  obtain ⟨i, hi, hail, haiu⟩ :=
    exists_nat_cell n (goldbachB9AlphaGridStep_pos hn) halow haup
  obtain ⟨j, hj, hbjl, hbju⟩ :=
    exists_nat_cell n (goldbachB9BetaGridStep_pos hn) hblow hbup
  have hal : goldbachB9AlphaGridPoint n i < primeLogExponent N rs.1 := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using hail
  have hau : primeLogExponent N rs.1 ≤ goldbachB9AlphaGridPoint n (i + 1) := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using haiu
  have hbl : goldbachB9BetaGridPoint n j < primeLogExponent N rs.2 := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbjl
  have hbu : primeLogExponent N rs.2 ≤ goldbachB9BetaGridPoint n (j + 1) := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbju
  refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), mem_goldbachB9LogGridCells_iff.mpr ?_, ?_⟩
  · exact ⟨hlow.trans hau, hsecond.trans hbu, by dsimp; linarith⟩
  · exact ⟨hal, hau, hbl, hbu⟩

theorem goldbachB9PairLogKernel_le_logGridMajorant
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) :
    goldbachB9PairLogKernel N ≤ goldbachB9LogGridMajorant n N := by
  have hcoverSum : goldbachB9PairLogKernel N ≤
      ∑ q ∈ goldbachB9LogGridCells n,
        goldbachB9PairLogKernelRectangleContribution N
          (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
          (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) := by
    rw [goldbachB9PairLogKernel_eq_logCoordinateSum]
    calc
      _ ≤ ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
          ∑ q ∈ goldbachB9LogGridCells n,
            if LiuPairInLogRectangle N
                (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
                (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) rs
              then liuPairLogKernel N rs else 0 := by
        apply Finset.sum_le_sum
        intro rs hrs
        obtain ⟨q, hq, hrect⟩ := goldbachB9Pairs_covered_by_logGrid n N hn hN hrs
        have hnonneg : ∀ q' ∈ goldbachB9LogGridCells n,
            0 ≤ if LiuPairInLogRectangle N
                (goldbachB9AlphaGridPoint n q'.1) (goldbachB9AlphaGridPoint n (q'.1 + 1))
                (goldbachB9BetaGridPoint n q'.2) (goldbachB9BetaGridPoint n (q'.2 + 1)) rs
              then liuPairLogKernel N rs else 0 := by
          intro q' _
          split_ifs
          · exact goldbachB9PairLogKernelTerm_nonneg hN hrs
          · exact le_rfl
        have hsingle := Finset.single_le_sum hnonneg hq
        simpa only [if_pos hrect] using hsingle
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        unfold goldbachB9PairLogKernelRectangleContribution goldbachB9PairsInLogRectangle
        rw [Finset.sum_filter]
  exact hcoverSum.trans (Finset.sum_le_sum fun q _ =>
    goldbachB9PairLogKernelRectangleContribution_le N hN _ _ _ _
      (goldbachB9LogGridCell_upperCorner_lt_one hn q))

/-- Only N tends to infinity here; its threshold may depend on n. -/
theorem tendsto_goldbachB9LogGridMajorant (n : ℕ) (hn : 0 < n) :
    Tendsto (goldbachB9LogGridMajorant n) atTop (nhds (goldbachB9LogGridUpperSum n)) := by
  unfold goldbachB9LogGridMajorant goldbachB9LogGridUpperSum
  apply tendsto_weighted_sum_primeReciprocalLogRectangle
  · intro q _
    exact goldbachB9AlphaGridPoint_pos n q.1
  · intro q _
    exact goldbachB9AlphaGridPoint_lt_succ hn
  · intro q _
    exact goldbachB9BetaGridPoint_pos n q.2
  · intro q _
    exact goldbachB9BetaGridPoint_lt_succ hn

theorem goldbachB9PairLogKernel_le_gridUpperSum_eventually
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB9PairLogKernel N ≤ goldbachB9LogGridUpperSum n + η := by
  have hc := (Metric.tendsto_nhds.1 (tendsto_goldbachB9LogGridMajorant n hn)) η hη
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hc
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by have := (le_max_left 4 N₁).trans hN; omega
  have hh : |goldbachB9LogGridMajorant n N - goldbachB9LogGridUpperSum n| < η := by
    simpa only [Real.dist_eq] using hN₁ N ((le_max_right _ _).trans hN)
  exact (goldbachB9PairLogKernel_le_logGridMajorant n N hn hN2).trans (by
    have hp := (abs_lt.mp hh).2
    linarith)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig