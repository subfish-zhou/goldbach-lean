import MathlibNt.SieveTheory.LiLiuGoldbachB8LogKernel
import MathlibNt.SieveTheory.LiuPrimePairLogGrid

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

noncomputable local instance instDecidablePropB8LogGrid (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def goldbachB8AlphaGridWidth : ℝ := 1 / 12

noncomputable def goldbachB8BetaGridWidth : ℝ := 5 / 44

noncomputable def goldbachB8AlphaGridPoint (n i : ℕ) : ℝ :=
  1 / 4 + (i : ℝ) / (n : ℝ) * goldbachB8AlphaGridWidth

noncomputable def goldbachB8BetaGridPoint (n j : ℕ) : ℝ :=
  1 / 4 + (j : ℝ) / (n : ℝ) * goldbachB8BetaGridWidth

noncomputable def goldbachB8AlphaGridStep (n : ℕ) : ℝ :=
  goldbachB8AlphaGridWidth / n

noncomputable def goldbachB8BetaGridStep (n : ℕ) : ℝ :=
  goldbachB8BetaGridWidth / n

/-- An outer selection sufficient for the closed B8 triangle; not an intersection test. -/
noncomputable def goldbachB8LogGridCells (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q =>
    goldbachB8Gamma ≤ goldbachB8AlphaGridPoint n (q.1 + 1) ∧
      goldbachB8AlphaGridPoint n q.1 < goldbachB8BetaGridPoint n (q.2 + 1) ∧
      goldbachB8AlphaGridPoint n q.1 + 2 * goldbachB8BetaGridPoint n q.2 < 1

noncomputable def goldbachB8LogGridMajorant (n N : ℕ) : ℝ :=
  ∑ q ∈ goldbachB8LogGridCells n,
    (1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1))) *
      primeReciprocalLogRectangle N
        (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1))
        (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1))

/-- A named finite upper sum only; no integral or limit assertion is made here. -/
noncomputable def goldbachB8LogGridUpperSum (n : ℕ) : ℝ :=
  ∑ q ∈ goldbachB8LogGridCells n,
    (1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1))) *
      logarithmicRectangleMass
        (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1))
        (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1))

theorem mem_goldbachB8LogGridCells_iff {n : ℕ} {q : Fin n × Fin n} :
    q ∈ goldbachB8LogGridCells n ↔
      goldbachB8Gamma ≤ goldbachB8AlphaGridPoint n (q.1 + 1) ∧
        goldbachB8AlphaGridPoint n q.1 < goldbachB8BetaGridPoint n (q.2 + 1) ∧
        goldbachB8AlphaGridPoint n q.1 + 2 * goldbachB8BetaGridPoint n q.2 < 1 := by
  simp only [goldbachB8LogGridCells, Finset.mem_filter, Finset.mem_univ, true_and]

theorem goldbachB8AlphaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < goldbachB8AlphaGridStep n := by
  unfold goldbachB8AlphaGridStep goldbachB8AlphaGridWidth
  positivity

theorem goldbachB8BetaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < goldbachB8BetaGridStep n := by
  unfold goldbachB8BetaGridStep goldbachB8BetaGridWidth
  positivity

theorem goldbachB8AlphaGridPoint_eq_step (n i : ℕ) :
    goldbachB8AlphaGridPoint n i =
      1 / 4 + (i : ℝ) * goldbachB8AlphaGridStep n := by
  unfold goldbachB8AlphaGridPoint goldbachB8AlphaGridStep
  ring

theorem goldbachB8BetaGridPoint_eq_step (n i : ℕ) :
    goldbachB8BetaGridPoint n i =
      1 / 4 + (i : ℝ) * goldbachB8BetaGridStep n := by
  unfold goldbachB8BetaGridPoint goldbachB8BetaGridStep
  ring

theorem goldbachB8AlphaGridPoint_succ (n i : ℕ) :
    goldbachB8AlphaGridPoint n (i + 1) =
      goldbachB8AlphaGridPoint n i + goldbachB8AlphaGridStep n := by
  rw [goldbachB8AlphaGridPoint_eq_step, goldbachB8AlphaGridPoint_eq_step]
  push_cast
  ring

theorem goldbachB8BetaGridPoint_succ (n i : ℕ) :
    goldbachB8BetaGridPoint n (i + 1) =
      goldbachB8BetaGridPoint n i + goldbachB8BetaGridStep n := by
  rw [goldbachB8BetaGridPoint_eq_step, goldbachB8BetaGridPoint_eq_step]
  push_cast
  ring

theorem goldbachB8AlphaGridPoint_pos (n i : ℕ) :
    0 < goldbachB8AlphaGridPoint n i := by
  unfold goldbachB8AlphaGridPoint goldbachB8AlphaGridWidth
  positivity

theorem goldbachB8BetaGridPoint_pos (n i : ℕ) :
    0 < goldbachB8BetaGridPoint n i := by
  unfold goldbachB8BetaGridPoint goldbachB8BetaGridWidth
  positivity

theorem goldbachB8AlphaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB8AlphaGridPoint n i < goldbachB8AlphaGridPoint n (i + 1) := by
  rw [goldbachB8AlphaGridPoint_succ]
  exact lt_add_of_pos_right _ (goldbachB8AlphaGridStep_pos hn)

theorem goldbachB8BetaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB8BetaGridPoint n i < goldbachB8BetaGridPoint n (i + 1) := by
  rw [goldbachB8BetaGridPoint_succ]
  exact lt_add_of_pos_right _ (goldbachB8BetaGridStep_pos hn)

theorem goldbachB8AlphaGridPoint_mono {n i j : ℕ} (hn : 0 < n) (hij : i ≤ j) :
    goldbachB8AlphaGridPoint n i ≤ goldbachB8AlphaGridPoint n j := by
  rw [goldbachB8AlphaGridPoint_eq_step, goldbachB8AlphaGridPoint_eq_step]
  have h := mul_le_mul_of_nonneg_right
    (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) (goldbachB8AlphaGridStep_pos hn).le
  linarith

theorem goldbachB8BetaGridPoint_mono {n i j : ℕ} (hn : 0 < n) (hij : i ≤ j) :
    goldbachB8BetaGridPoint n i ≤ goldbachB8BetaGridPoint n j := by
  rw [goldbachB8BetaGridPoint_eq_step, goldbachB8BetaGridPoint_eq_step]
  have h := mul_le_mul_of_nonneg_right
    (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) (goldbachB8BetaGridStep_pos hn).le
  linarith

theorem goldbachB8AlphaGridPoint_end {n : ℕ} (hn : 0 < n) :
    goldbachB8AlphaGridPoint n n = (1 / 3 : ℝ) := by
  unfold goldbachB8AlphaGridPoint goldbachB8AlphaGridWidth
  rw [div_self (Nat.cast_ne_zero.mpr hn.ne')]
  norm_num

theorem goldbachB8BetaGridPoint_end {n : ℕ} (hn : 0 < n) :
    goldbachB8BetaGridPoint n n = (4 / 11 : ℝ) := by
  unfold goldbachB8BetaGridPoint goldbachB8BetaGridWidth
  rw [div_self (Nat.cast_ne_zero.mpr hn.ne')]
  norm_num

theorem goldbachB8AlphaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    goldbachB8AlphaGridPoint n (i + 1) ≤ (1 / 3 : ℝ) := by
  rw [← goldbachB8AlphaGridPoint_end hn]
  exact goldbachB8AlphaGridPoint_mono hn (Nat.succ_le_iff.mpr hi)

theorem goldbachB8BetaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    goldbachB8BetaGridPoint n (i + 1) ≤ (4 / 11 : ℝ) := by
  rw [← goldbachB8BetaGridPoint_end hn]
  exact goldbachB8BetaGridPoint_mono hn (Nat.succ_le_iff.mpr hi)

/-- The gap holds on the entire ambient grid, not just selected cells. -/
theorem goldbachB8LogGridCell_cornerGap_ge {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    (10 / 33 : ℝ) ≤ 1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1) := by
  have ha := goldbachB8AlphaGridPoint_succ_le_end hn q.1.isLt
  have hb := goldbachB8BetaGridPoint_succ_le_end hn q.2.isLt
  linarith

theorem goldbachB8LogGridCell_cornerGap_pos {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    0 < 1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1) :=
  lt_of_lt_of_le (by norm_num) (goldbachB8LogGridCell_cornerGap_ge hn q)

theorem goldbachB8LogGridCell_upperCorner_lt_one
    {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    goldbachB8AlphaGridPoint n (q.1 + 1) +
      goldbachB8BetaGridPoint n (q.2 + 1) < 1 := by
  linarith [goldbachB8LogGridCell_cornerGap_pos hn q]

/-- The two `Ioc` locations retain grid points and every closed source boundary. -/
theorem goldbachB8Pairs_covered_by_logGrid
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    ∃ q ∈ goldbachB8LogGridCells n,
      LiuPairInLogRectangle N
        (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1))
        (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1)) rs := by
  obtain ⟨hlow, hfirst, horder, htriangle⟩ := goldbachB8Pair_logGeometry hN hrs
  have halow : (1 / 4 : ℝ) < primeLogExponent N rs.1 := by
    dsimp [goldbachB8Gamma] at hlow
    linarith
  have hblow : (1 / 4 : ℝ) < primeLogExponent N rs.2 := halow.trans_le horder
  have haup : primeLogExponent N rs.1 ≤
      1 / 4 + (n : ℝ) * goldbachB8AlphaGridStep n := by
    rw [← goldbachB8AlphaGridPoint_eq_step, goldbachB8AlphaGridPoint_end hn]
    exact hfirst
  have hbup : primeLogExponent N rs.2 ≤
      1 / 4 + (n : ℝ) * goldbachB8BetaGridStep n := by
    rw [← goldbachB8BetaGridPoint_eq_step, goldbachB8BetaGridPoint_end hn]
    exact goldbachB8PrimeLogExponent_second_le_upper hN hrs
  obtain ⟨i, hi, hail, haiu⟩ :=
    exists_nat_cell n (goldbachB8AlphaGridStep_pos hn) halow haup
  obtain ⟨j, hj, hbjl, hbju⟩ :=
    exists_nat_cell n (goldbachB8BetaGridStep_pos hn) hblow hbup
  have hal : goldbachB8AlphaGridPoint n i < primeLogExponent N rs.1 := by
    simpa only [goldbachB8AlphaGridPoint_eq_step] using hail
  have hau : primeLogExponent N rs.1 ≤ goldbachB8AlphaGridPoint n (i + 1) := by
    simpa only [goldbachB8AlphaGridPoint_eq_step] using haiu
  have hbl : goldbachB8BetaGridPoint n j < primeLogExponent N rs.2 := by
    simpa only [goldbachB8BetaGridPoint_eq_step] using hbjl
  have hbu : primeLogExponent N rs.2 ≤ goldbachB8BetaGridPoint n (j + 1) := by
    simpa only [goldbachB8BetaGridPoint_eq_step] using hbju
  refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), mem_goldbachB8LogGridCells_iff.mpr ?_, ?_⟩
  · exact ⟨hlow.trans hau, hal.trans_le (horder.trans hbu), by dsimp; linarith⟩
  · exact ⟨hal, hau, hbl, hbu⟩

/-- The actual finite B8 kernel is bounded by the fixed, closed-boundary grid majorant. -/
theorem goldbachB8PairLogKernel_le_logGridMajorant
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) :
    goldbachB8PairLogKernel N ≤ goldbachB8LogGridMajorant n N := by
  have hcoverSum : goldbachB8PairLogKernel N ≤
      ∑ q ∈ goldbachB8LogGridCells n,
        goldbachB8PairLogKernelRectangleContribution N
          (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1))
          (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1)) := by
    rw [goldbachB8PairLogKernel_eq_logCoordinateSum]
    calc
      _ ≤ ∑ rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ)),
          ∑ q ∈ goldbachB8LogGridCells n,
            if LiuPairInLogRectangle N
                (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1))
                (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1)) rs
              then liuPairLogKernel N rs else 0 := by
        apply Finset.sum_le_sum
        intro rs hrs
        obtain ⟨q, hq, hrect⟩ := goldbachB8Pairs_covered_by_logGrid n N hn hN hrs
        have hnonneg : ∀ q' ∈ goldbachB8LogGridCells n,
            0 ≤ if LiuPairInLogRectangle N
                (goldbachB8AlphaGridPoint n q'.1) (goldbachB8AlphaGridPoint n (q'.1 + 1))
                (goldbachB8BetaGridPoint n q'.2) (goldbachB8BetaGridPoint n (q'.2 + 1)) rs
              then liuPairLogKernel N rs else 0 := by
          intro q' _
          split_ifs
          · exact goldbachB8PairLogKernelTerm_nonneg hN hrs
          · exact le_rfl
        have hsingle := Finset.single_le_sum hnonneg hq
        simpa only [if_pos hrect] using hsingle
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        unfold goldbachB8PairLogKernelRectangleContribution goldbachB8PairsInLogRectangle
        rw [Finset.sum_filter]
  exact hcoverSum.trans (Finset.sum_le_sum fun q _ =>
    goldbachB8PairLogKernelRectangleContribution_le N hN _ _ _ _
      (goldbachB8LogGridCell_upperCorner_lt_one hn q))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig