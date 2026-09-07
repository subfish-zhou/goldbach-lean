import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridLimit
import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstMainMass

open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Filter Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

noncomputable local instance instDecidablePropB9HighFirstLogGrid (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def goldbachB9HighLogGridCells (n : ℕ) : Finset (Fin n × Fin n) :=
  (goldbachB9LogGridCells n).filter
    (fun q => (1 / 10 : ℝ) ≤ goldbachB9AlphaGridPoint n (q.1 + 1))

noncomputable def goldbachB9HighLogGridMajorant (n N : ℕ) : ℝ :=
  ∑ q ∈ goldbachB9HighLogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      primeReciprocalLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))

noncomputable def goldbachB9HighLogGridUpperSum (n : ℕ) : ℝ :=
  ∑ q ∈ goldbachB9HighLogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      logarithmicRectangleMass
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))

theorem goldbachB9HighLogGridCells_subset (n : ℕ) :
    goldbachB9HighLogGridCells n ⊆ goldbachB9LogGridCells n :=
  Finset.filter_subset _ _

theorem mem_goldbachB9HighLogGridCells_iff {n : ℕ} {q : Fin n × Fin n} :
    q ∈ goldbachB9HighLogGridCells n ↔
      (1 / 10 : ℝ) ≤ goldbachB9AlphaGridPoint n (q.1 + 1) ∧
        (1 / 3 : ℝ) ≤ goldbachB9BetaGridPoint n (q.2 + 1) ∧
        goldbachB9AlphaGridPoint n q.1 + 2 * goldbachB9BetaGridPoint n q.2 < 1 := by
  rw [goldbachB9HighLogGridCells, Finset.mem_filter, mem_goldbachB9LogGridCells_iff]
  constructor
  · rintro ⟨⟨_, hb, ht⟩, ha⟩
    exact ⟨ha, hb, ht⟩
  · rintro ⟨ha, hb, ht⟩
    exact ⟨⟨by linarith, hb, ht⟩, ha⟩

theorem goldbachB9HighPairs_subset (N : ℕ) (hN : 2 ≤ N) :
    goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆
      goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  rw [goldbachC10HighFirstPairs_eq_filter N hN, goldbachC9Pairs_eq_C10Pairs]
  exact Finset.filter_subset _ _

theorem goldbachB9HighPair_logGeometry
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    (1 / 10 : ℝ) ≤ primeLogExponent N rs.1 ∧
      primeLogExponent N rs.1 ≤ (1 / 3 : ℝ) ∧
      (1 / 3 : ℝ) ≤ primeLogExponent N rs.2 ∧
      primeLogExponent N rs.1 + 2 * primeLogExponent N rs.2 ≤ 1 := by
  obtain ⟨_, _, _, hfirstPow, _, _, _⟩ := mem_goldbachC10Pairs_iff.mp hrs
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hfirstLog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hfirstPow
  rw [Real.log_rpow hNp] at hfirstLog
  exact ⟨(le_div_iff₀ hlogN).mpr hfirstLog,
    (goldbachB9Pair_logGeometry hN (goldbachB9HighPairs_subset N hN hrs)).2⟩

theorem goldbachK9High_eq_logCoordinateSum (N : ℕ) (hN : 2 ≤ N) :
    goldbachK9High N =
      ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), liuPairLogKernel N rs := by
  unfold goldbachK9High
  exact Finset.sum_congr rfl (fun _ hrs =>
    goldbachB9PairLogKernelTerm_eq (goldbachB9HighPairs_subset N hN hrs))

/-- The actual closed first-prime endpoint belongs to the selected cover. -/
theorem goldbachB9HighPairs_covered_by_logGrid
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ q ∈ goldbachB9HighLogGridCells n,
      LiuPairInLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) rs := by
  obtain ⟨q, hq, hrect⟩ :=
    goldbachB9Pairs_covered_by_logGrid n N hn hN (goldbachB9HighPairs_subset N hN hrs)
  exact ⟨q, Finset.mem_filter.mpr
    ⟨hq, (goldbachB9HighPair_logGeometry hN hrs).1.trans hrect.2.1⟩, hrect⟩

/-- Full-family rectangle estimates are used only inside the high selection. -/
theorem goldbachK9High_le_logGridMajorant
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) :
    goldbachK9High N ≤ goldbachB9HighLogGridMajorant n N := by
  rw [goldbachK9High_eq_logCoordinateSum N hN]
  calc
    _ ≤ ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        ∑ q ∈ goldbachB9HighLogGridCells n,
          if LiuPairInLogRectangle N
              (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
              (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) rs
            then liuPairLogKernel N rs else 0 := by
      apply Finset.sum_le_sum
      intro rs hrs
      obtain ⟨q, hq, hrect⟩ := goldbachB9HighPairs_covered_by_logGrid n N hn hN hrs
      have hnonneg : ∀ q' ∈ goldbachB9HighLogGridCells n,
          0 ≤ if LiuPairInLogRectangle N
              (goldbachB9AlphaGridPoint n q'.1) (goldbachB9AlphaGridPoint n (q'.1 + 1))
              (goldbachB9BetaGridPoint n q'.2) (goldbachB9BetaGridPoint n (q'.2 + 1)) rs
            then liuPairLogKernel N rs else 0 := by
        intro q' _
        split_ifs
        · exact goldbachB9PairLogKernelTerm_nonneg hN (goldbachB9HighPairs_subset N hN hrs)
        · exact le_rfl
      simpa only [if_pos hrect] using Finset.single_le_sum hnonneg hq
    _ ≤ ∑ q ∈ goldbachB9HighLogGridCells n,
        goldbachB9PairLogKernelRectangleContribution N
          (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1))
          (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro q _
      unfold goldbachB9PairLogKernelRectangleContribution goldbachB9PairsInLogRectangle
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg (goldbachB9HighPairs_subset N hN)
      intro rs hrs _
      split_ifs
      · exact goldbachB9PairLogKernelTerm_nonneg hN hrs
      · exact le_rfl
    _ ≤ _ := Finset.sum_le_sum fun q _ =>
      goldbachB9PairLogKernelRectangleContribution_le N hN _ _ _ _
        (goldbachB9LogGridCell_upperCorner_lt_one hn q)

theorem goldbachB9HighLogGridMajorant_eq_primeReciprocalProducts (n N : ℕ) :
    goldbachB9HighLogGridMajorant n N =
      ∑ q ∈ goldbachB9HighLogGridCells n,
        (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
          goldbachB9BetaGridPoint n (q.2 + 1))) *
          (PrimeReciprocalLogScale.primeReciprocalLogInterval N
            (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1)) *
          PrimeReciprocalLogScale.primeReciprocalLogInterval N
            (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))) := by
  simp only [goldbachB9HighLogGridMajorant, primeReciprocalLogRectangle_eq_mul]

/-- Apply Mertens to this finite weighted sum, not to a full-sum limit. -/
theorem tendsto_goldbachB9HighLogGridMajorant (n : ℕ) (hn : 0 < n) :
    Tendsto (goldbachB9HighLogGridMajorant n) atTop
      (nhds (goldbachB9HighLogGridUpperSum n)) := by
  unfold goldbachB9HighLogGridMajorant goldbachB9HighLogGridUpperSum
  apply tendsto_weighted_sum_primeReciprocalLogRectangle
  · intro q _
    exact goldbachB9AlphaGridPoint_pos n q.1
  · intro q _
    exact goldbachB9AlphaGridPoint_lt_succ hn
  · intro q _
    exact goldbachB9BetaGridPoint_pos n q.2
  · intro q _
    exact goldbachB9BetaGridPoint_lt_succ hn

theorem goldbachK9High_le_gridUpperSum_eventually
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachK9High N ≤ goldbachB9HighLogGridUpperSum n + η := by
  have hc := (Metric.tendsto_nhds.1 (tendsto_goldbachB9HighLogGridMajorant n hn)) η hη
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hc
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by have := (le_max_left 4 N₁).trans hN; omega
  have hh : |goldbachB9HighLogGridMajorant n N - goldbachB9HighLogGridUpperSum n| < η := by
    simpa only [Real.dist_eq] using hN₁ N ((le_max_right _ _).trans hN)
  exact (goldbachK9High_le_logGridMajorant n N hn hN2).trans (by
    have hp := (abs_lt.mp hh).2
    linarith)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig