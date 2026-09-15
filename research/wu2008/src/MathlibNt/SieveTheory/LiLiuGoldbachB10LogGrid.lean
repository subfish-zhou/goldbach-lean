import MathlibNt.SieveTheory.LiLiuGoldbachB10LogKernel
import MathlibNt.SieveTheory.LiuPrimePairLogGrid

open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Filter Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

/-- The ambient left endpoint used to cover the closed lower bound `u = β`. -/
noncomputable def goldbachB10AlphaGridStart : ℝ := 1 / 10

/-- The ambient lower endpoint used to cover the closed lower bound `v = γ`. -/
noncomputable def goldbachB10BetaGridStart : ℝ := 1 / 4

/-- The exact top endpoint forced by `u ≥ β` and `u + 2v ≤ 1`. -/
noncomputable def goldbachB10BetaGridEnd : ℝ := 29 / 66

/-- The `u`-width of the ambient B10 logarithmic box. -/
noncomputable def goldbachB10AlphaGridWidth : ℝ := 19 / 110

/-- The `v`-width of the ambient B10 logarithmic box. -/
noncomputable def goldbachB10BetaGridWidth : ℝ := 25 / 132

/-- The `i`th point of the ambient `u`-grid from `1/10` to `3/11`. -/
noncomputable def goldbachB10AlphaGridPoint (n i : ℕ) : ℝ :=
  goldbachB10AlphaGridStart + (i : ℝ) / (n : ℝ) * goldbachB10AlphaGridWidth

/-- The `j`th point of the ambient `v`-grid from `1/4` to `29/66`. -/
noncomputable def goldbachB10BetaGridPoint (n j : ℕ) : ℝ :=
  goldbachB10BetaGridStart + (j : ℝ) / (n : ℝ) * goldbachB10BetaGridWidth

/-- The `u`-step of the ambient B10 logarithmic grid. -/
noncomputable def goldbachB10AlphaGridStep (n : ℕ) : ℝ :=
  goldbachB10AlphaGridWidth / n

/-- The `v`-step of the ambient B10 logarithmic grid. -/
noncomputable def goldbachB10BetaGridStep (n : ℕ) : ℝ :=
  goldbachB10BetaGridWidth / n

/-- The selected cells are those which intersect the closed-lower B10 source
triangle `β ≤ u`, `γ ≤ v`, `u + 2v ≤ 1`. -/
noncomputable def goldbachB10LogGridCells (n : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun q =>
    goldbachB10Beta ≤ goldbachB10AlphaGridPoint n (q.1 + 1) ∧
      goldbachB10Gamma ≤ goldbachB10BetaGridPoint n (q.2 + 1) ∧
      goldbachB10AlphaGridPoint n q.1 + 2 * goldbachB10BetaGridPoint n q.2 < 1

/-- The finite-`N` upper-corner majorant on the selected B10 cells. -/
noncomputable def goldbachB10LogGridMajorant (n N : ℕ) : ℝ :=
  ∑ q ∈ goldbachB10LogGridCells n,
    (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1))) *
      primeReciprocalLogRectangle N
        (goldbachB10AlphaGridPoint n q.1) (goldbachB10AlphaGridPoint n (q.1 + 1))
        (goldbachB10BetaGridPoint n q.2) (goldbachB10BetaGridPoint n (q.2 + 1))

/-- The fixed-grid logarithmic upper sum corresponding to the B10 majorant. -/
noncomputable def goldbachB10LogGridUpperSum (n : ℕ) : ℝ :=
  ∑ q ∈ goldbachB10LogGridCells n,
    (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1))) *
      logarithmicRectangleMass
        (goldbachB10AlphaGridPoint n q.1) (goldbachB10AlphaGridPoint n (q.1 + 1))
        (goldbachB10BetaGridPoint n q.2) (goldbachB10BetaGridPoint n (q.2 + 1))

private lemma goldbachB10Beta_gt_alphaGridStart :
    goldbachB10AlphaGridStart < goldbachB10Beta := by
  dsimp [goldbachB10AlphaGridStart, goldbachB10Beta]
  norm_num

private lemma goldbachB10Gamma_gt_betaGridStart :
    goldbachB10BetaGridStart < goldbachB10Gamma := by
  dsimp [goldbachB10BetaGridStart, goldbachB10Gamma]
  norm_num

private lemma goldbachB10Gamma_eq_alphaGridEnd :
    goldbachB10AlphaGridStart + goldbachB10AlphaGridWidth = goldbachB10Gamma := by
  dsimp [goldbachB10AlphaGridStart, goldbachB10AlphaGridWidth, goldbachB10Gamma]
  ring

private lemma goldbachB10BetaGridEnd_eq :
    goldbachB10BetaGridStart + goldbachB10BetaGridWidth = goldbachB10BetaGridEnd := by
  dsimp [goldbachB10BetaGridStart, goldbachB10BetaGridWidth, goldbachB10BetaGridEnd]
  ring

lemma goldbachB10AlphaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < goldbachB10AlphaGridStep n := by
  unfold goldbachB10AlphaGridStep goldbachB10AlphaGridWidth
  positivity

lemma goldbachB10BetaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < goldbachB10BetaGridStep n := by
  unfold goldbachB10BetaGridStep goldbachB10BetaGridWidth
  positivity

lemma goldbachB10AlphaGridPoint_eq_step {n i : ℕ} (hn : 0 < n) :
    goldbachB10AlphaGridPoint n i =
      goldbachB10AlphaGridStart + (i : ℝ) * goldbachB10AlphaGridStep n := by
  unfold goldbachB10AlphaGridPoint goldbachB10AlphaGridStart goldbachB10AlphaGridStep
    goldbachB10AlphaGridWidth
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

lemma goldbachB10BetaGridPoint_eq_step {n i : ℕ} (hn : 0 < n) :
    goldbachB10BetaGridPoint n i =
      goldbachB10BetaGridStart + (i : ℝ) * goldbachB10BetaGridStep n := by
  unfold goldbachB10BetaGridPoint goldbachB10BetaGridStart goldbachB10BetaGridStep
    goldbachB10BetaGridWidth
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

lemma goldbachB10AlphaGridPoint_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB10AlphaGridPoint n (i + 1) =
      goldbachB10AlphaGridPoint n i + goldbachB10AlphaGridStep n := by
  rw [goldbachB10AlphaGridPoint_eq_step hn, goldbachB10AlphaGridPoint_eq_step hn]
  push_cast
  ring

lemma goldbachB10BetaGridPoint_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB10BetaGridPoint n (i + 1) =
      goldbachB10BetaGridPoint n i + goldbachB10BetaGridStep n := by
  rw [goldbachB10BetaGridPoint_eq_step hn, goldbachB10BetaGridPoint_eq_step hn]
  push_cast
  ring

lemma goldbachB10AlphaGridPoint_pos {n i : ℕ} (hn : 0 < n) :
    0 < goldbachB10AlphaGridPoint n i := by
  rw [goldbachB10AlphaGridPoint_eq_step hn]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hs := (goldbachB10AlphaGridStep_pos hn).le
  dsimp [goldbachB10AlphaGridStart]
  nlinarith [mul_nonneg hi hs]

lemma goldbachB10BetaGridPoint_pos {n i : ℕ} (hn : 0 < n) :
    0 < goldbachB10BetaGridPoint n i := by
  rw [goldbachB10BetaGridPoint_eq_step hn]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hs := (goldbachB10BetaGridStep_pos hn).le
  dsimp [goldbachB10BetaGridStart]
  nlinarith [mul_nonneg hi hs]

lemma goldbachB10AlphaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB10AlphaGridPoint n i < goldbachB10AlphaGridPoint n (i + 1) := by
  rw [goldbachB10AlphaGridPoint_succ hn]
  exact lt_add_of_pos_right _ (goldbachB10AlphaGridStep_pos hn)

lemma goldbachB10BetaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    goldbachB10BetaGridPoint n i < goldbachB10BetaGridPoint n (i + 1) := by
  rw [goldbachB10BetaGridPoint_succ hn]
  exact lt_add_of_pos_right _ (goldbachB10BetaGridStep_pos hn)

lemma goldbachB10AlphaGridPoint_mono {n i j : ℕ}
    (hn : 0 < n) (hij : i ≤ j) :
    goldbachB10AlphaGridPoint n i ≤ goldbachB10AlphaGridPoint n j := by
  rw [goldbachB10AlphaGridPoint_eq_step hn, goldbachB10AlphaGridPoint_eq_step hn]
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have := mul_le_mul_of_nonneg_right hij' (goldbachB10AlphaGridStep_pos hn).le
  linarith

lemma goldbachB10BetaGridPoint_mono {n i j : ℕ}
    (hn : 0 < n) (hij : i ≤ j) :
    goldbachB10BetaGridPoint n i ≤ goldbachB10BetaGridPoint n j := by
  rw [goldbachB10BetaGridPoint_eq_step hn, goldbachB10BetaGridPoint_eq_step hn]
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have := mul_le_mul_of_nonneg_right hij' (goldbachB10BetaGridStep_pos hn).le
  linarith

lemma goldbachB10AlphaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    goldbachB10AlphaGridPoint n (i + 1) ≤ goldbachB10Gamma := by
  have hin : ((i + 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ((i + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnreal).mpr hin
  unfold goldbachB10AlphaGridPoint
  rw [← goldbachB10Gamma_eq_alphaGridEnd]
  have hmul :
      ((i + 1 : ℕ) : ℝ) / (n : ℝ) * goldbachB10AlphaGridWidth ≤
        goldbachB10AlphaGridWidth := by
    simpa using
      (mul_le_mul_of_nonneg_right hratio (by
        dsimp [goldbachB10AlphaGridWidth]
        positivity : 0 ≤ goldbachB10AlphaGridWidth))
  linarith

lemma goldbachB10BetaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    goldbachB10BetaGridPoint n (i + 1) ≤ goldbachB10BetaGridEnd := by
  have hin : ((i + 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ((i + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnreal).mpr hin
  unfold goldbachB10BetaGridPoint
  rw [← goldbachB10BetaGridEnd_eq]
  have hmul :
      ((i + 1 : ℕ) : ℝ) / (n : ℝ) * goldbachB10BetaGridWidth ≤
        goldbachB10BetaGridWidth := by
    simpa using
      (mul_le_mul_of_nonneg_right hratio (by
        dsimp [goldbachB10BetaGridWidth]
        positivity : 0 ≤ goldbachB10BetaGridWidth))
  linarith

/-- Every selected cell has its upper-right corner strictly below the kernel
singularity `u + v = 1`. -/
theorem goldbachB10LogGridCell_upperCorner_lt_one
    {n : ℕ} (hn : 0 < n) {q : Fin n × Fin n}
    (_hq : q ∈ goldbachB10LogGridCells n) :
    goldbachB10AlphaGridPoint n (q.1 + 1) +
      goldbachB10BetaGridPoint n (q.2 + 1) < 1 := by
  have hα := goldbachB10AlphaGridPoint_succ_le_end hn q.1.isLt
  have hβ := goldbachB10BetaGridPoint_succ_le_end hn q.2.isLt
  dsimp [goldbachB10Gamma, goldbachB10BetaGridEnd] at hα hβ ⊢
  linarith

/-- Every actual `C10` pair lies in a selected ambient B10 logarithmic cell. -/
theorem goldbachB10Pairs_covered_by_logGrid
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    ∃ q ∈ goldbachB10LogGridCells n,
      goldbachB10PairInLogRectangle N
        (goldbachB10AlphaGridPoint n q.1) (goldbachB10AlphaGridPoint n (q.1 + 1))
        (goldbachB10BetaGridPoint n q.2) (goldbachB10BetaGridPoint n (q.2 + 1)) rs := by
  have hαlower : goldbachB10AlphaGridStart < primeLogExponent N rs.1 := by
    have hβ : goldbachB10Beta ≤ primeLogExponent N rs.1 :=
      goldbachB10PrimeLogExponent_ge_beta hN hrs
    linarith [goldbachB10Beta_gt_alphaGridStart]
  have hβlower : goldbachB10BetaGridStart < primeLogExponent N rs.2 := by
    have hγ : goldbachB10Gamma ≤ primeLogExponent N rs.2 := by
      rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, hsPrime, _, _, _, hcs, _⟩
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hspos : (0 : ℝ) < rs.2 := by exact_mod_cast hsPrime.pos
      have hlogN : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hlog : Real.log ((N : ℝ) ^ goldbachB10Gamma) ≤ Real.log rs.2 :=
        Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hcs
      rw [Real.log_rpow hNpos] at hlog
      unfold primeLogExponent
      exact (le_div_iff₀ hlogN).2 hlog
    linarith [goldbachB10Gamma_gt_betaGridStart]
  have hαupper :
      primeLogExponent N rs.1 ≤
        goldbachB10AlphaGridStart + (n : ℝ) * goldbachB10AlphaGridStep n := by
    rw [show goldbachB10AlphaGridStart + (n : ℝ) * goldbachB10AlphaGridStep n =
        goldbachB10Gamma by
      unfold goldbachB10AlphaGridStart goldbachB10AlphaGridStep goldbachB10AlphaGridWidth
      dsimp [goldbachB10Gamma]
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    exact goldbachB10PrimeLogExponent_le_gamma hN hrs
  have hβupper :
      primeLogExponent N rs.2 ≤
        goldbachB10BetaGridStart + (n : ℝ) * goldbachB10BetaGridStep n := by
    rw [show goldbachB10BetaGridStart + (n : ℝ) * goldbachB10BetaGridStep n =
        goldbachB10BetaGridEnd by
      unfold goldbachB10BetaGridStart goldbachB10BetaGridStep goldbachB10BetaGridWidth
        goldbachB10BetaGridEnd
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    exact goldbachB10PrimeLogExponent_second_le_upper hN hrs
  obtain ⟨i, hi, hαl, hαu⟩ :=
    exists_nat_cell n (goldbachB10AlphaGridStep_pos hn) hαlower hαupper
  obtain ⟨j, hj, hβl, hβu⟩ :=
    exists_nat_cell n (goldbachB10BetaGridStep_pos hn) hβlower hβupper
  let fi : Fin n := ⟨i, hi⟩
  let fj : Fin n := ⟨j, hj⟩
  have hαl' : goldbachB10AlphaGridPoint n fi < primeLogExponent N rs.1 := by
    simpa [fi, goldbachB10AlphaGridPoint_eq_step hn] using hαl
  have hαu' : primeLogExponent N rs.1 ≤ goldbachB10AlphaGridPoint n (fi + 1) := by
    simpa [fi, goldbachB10AlphaGridPoint_eq_step hn] using hαu
  have hβl' : goldbachB10BetaGridPoint n fj < primeLogExponent N rs.2 := by
    simpa [fj, goldbachB10BetaGridPoint_eq_step hn] using hβl
  have hβu' : primeLogExponent N rs.2 ≤ goldbachB10BetaGridPoint n (fj + 1) := by
    simpa [fj, goldbachB10BetaGridPoint_eq_step hn] using hβu
  have hright : goldbachB10Beta ≤ goldbachB10AlphaGridPoint n (fi + 1) := by
    exact (goldbachB10PrimeLogExponent_ge_beta hN hrs).trans hαu'
  have htop : goldbachB10Gamma ≤ goldbachB10BetaGridPoint n (fj + 1) := by
    have hγ : goldbachB10Gamma ≤ primeLogExponent N rs.2 := by
      rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, hsPrime, _, _, _, hcs, _⟩
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hspos : (0 : ℝ) < rs.2 := by exact_mod_cast hsPrime.pos
      have hlogN : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hlog : Real.log ((N : ℝ) ^ goldbachB10Gamma) ≤ Real.log rs.2 :=
        Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hcs
      rw [Real.log_rpow hNpos] at hlog
      unfold primeLogExponent
      exact (le_div_iff₀ hlogN).2 hlog
    exact hγ.trans hβu'
  have hselected :
      goldbachB10AlphaGridPoint n fi + 2 * goldbachB10BetaGridPoint n fj < 1 := by
    nlinarith [goldbachB10PrimeLogExponent_add_two_mul_le_one hN hrs]
  refine ⟨(fi, fj), ?_, ?_⟩
  · rw [goldbachB10LogGridCells, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hright, htop, hselected⟩
  · exact ⟨hαl', hαu', hβl', hβu'⟩

/-- The selected B10 logarithmic grid majorizes the full actual `C10`
logarithmic-kernel sum. -/
theorem goldbachB10PairLogKernelSum_le_logGridMajorant
    (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N) :
    goldbachB10PairLogKernelSum N ≤ goldbachB10LogGridMajorant n N := by
  classical
  unfold goldbachB10LogGridMajorant
  exact goldbachB10PairLogKernelSum_le_sum_rectangleMajorants_of_cover
    (goldbachB10LogGridCells n)
    (fun q => goldbachB10AlphaGridPoint n q.1)
    (fun q => goldbachB10AlphaGridPoint n (q.1 + 1))
    (fun q => goldbachB10BetaGridPoint n q.2)
    (fun q => goldbachB10BetaGridPoint n (q.2 + 1))
    N hN
    (fun q _ => goldbachB10AlphaGridPoint_pos hn)
    (fun q _ => goldbachB10AlphaGridPoint_lt_succ hn)
    (fun q _ => goldbachB10BetaGridPoint_pos hn)
    (fun q _ => goldbachB10BetaGridPoint_lt_succ hn)
    (fun q hq => goldbachB10LogGridCell_upperCorner_lt_one hn hq)
    (fun rs hrs => goldbachB10Pairs_covered_by_logGrid n N hn hN hrs)

/-- For every fixed positive grid size, the finite-`N` B10 majorant tends to
its logarithmic upper sum. -/
theorem tendsto_goldbachB10LogGridMajorant
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => goldbachB10LogGridMajorant n N) atTop
      (nhds (goldbachB10LogGridUpperSum n)) := by
  classical
  unfold goldbachB10LogGridMajorant goldbachB10LogGridUpperSum
  exact tendsto_weighted_sum_primeReciprocalLogRectangle
    (goldbachB10LogGridCells n)
    (fun q => 1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1)))
    (fun q => goldbachB10AlphaGridPoint n q.1)
    (fun q => goldbachB10AlphaGridPoint n (q.1 + 1))
    (fun q => goldbachB10BetaGridPoint n q.2)
    (fun q => goldbachB10BetaGridPoint n (q.2 + 1))
    (fun q _ => goldbachB10AlphaGridPoint_pos hn)
    (fun q _ => goldbachB10AlphaGridPoint_lt_succ hn)
    (fun q _ => goldbachB10BetaGridPoint_pos hn)
    (fun q _ => goldbachB10BetaGridPoint_lt_succ hn)

/-- Eventual epsilon form of fixed B10-grid convergence. -/
theorem eventually_abs_goldbachB10LogGridMajorant_sub_lt
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |goldbachB10LogGridMajorant n N - goldbachB10LogGridUpperSum n| < ε := by
  have h := tendsto_goldbachB10LogGridMajorant n hn
  rw [Metric.tendsto_nhds] at h
  filter_upwards [h ε hε] with N hN
  simpa only [Real.dist_eq] using hN

/-- Threshold form of fixed B10-grid convergence. -/
theorem exists_abs_goldbachB10LogGridMajorant_sub_lt
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |goldbachB10LogGridMajorant n N - goldbachB10LogGridUpperSum n| < ε := by
  simpa only [eventually_atTop] using
    eventually_abs_goldbachB10LogGridMajorant_sub_lt n hn hε

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig