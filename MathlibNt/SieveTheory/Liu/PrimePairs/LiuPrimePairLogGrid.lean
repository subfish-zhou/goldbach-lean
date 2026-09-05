import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairLogKernel

/-!
# A canonical logarithmic grid for Liu's prime pairs

This module partitions the fixed source box
`(1/10, 1/3] × (1/3, 9/20]` into an `n × n` grid.  Cells are selected from
their lower-left corners using the exact source boundary `α + 2β ≤ 1`.
The resulting finite rectangle majorant converges, for each fixed positive
`n`, to its logarithmic upper sum.

No limit as the mesh tends to zero is asserted here.
-/

open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open PrimeReciprocalLogRectangle

/-- The `i`th point of the canonical alpha grid from `1/10` to `1/3`. -/
noncomputable def liuAlphaGridPoint (n i : ℕ) : ℝ :=
  1 / 10 + (i : ℝ) / (n : ℝ) * (7 / 30)

/-- The `j`th point of the canonical beta grid from `1/3` to `9/20`. -/
noncomputable def liuBetaGridPoint (n j : ℕ) : ℝ :=
  1 / 3 + (j : ℝ) / (n : ℝ) * (7 / 60)

/-- The alpha width of a cell in the canonical grid. -/
noncomputable def liuAlphaGridStep (n : ℕ) : ℝ :=
  (7 / 30 : ℝ) / n

/-- The beta width of a cell in the canonical grid. -/
noncomputable def liuBetaGridStep (n : ℕ) : ℝ :=
  (7 / 60 : ℝ) / n

/-- The selected cells are those whose lower-left corner lies strictly below
the exact source line `β = (1 - α) / 2`. -/
noncomputable def liuLogGridCells (n : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun q =>
    liuBetaGridPoint n q.2 < (1 - liuAlphaGridPoint n q.1) / 2

/-- The finite-`N` upper-corner majorant on the selected canonical cells. -/
noncomputable def liuLogGridMajorant (n N : ℕ) : ℝ :=
  ∑ q ∈ liuLogGridCells n,
    (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1))) *
      primeReciprocalLogRectangle N
        (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1))
        (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1))

/-- The fixed-grid logarithmic upper sum corresponding to
`liuLogGridMajorant`. -/
noncomputable def liuLogGridUpperSum (n : ℕ) : ℝ :=
  ∑ q ∈ liuLogGridCells n,
    (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1))) *
      logarithmicRectangleMass
        (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1))
        (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1))

lemma liuAlphaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < liuAlphaGridStep n := by
  unfold liuAlphaGridStep
  positivity

lemma liuBetaGridStep_pos {n : ℕ} (hn : 0 < n) :
    0 < liuBetaGridStep n := by
  unfold liuBetaGridStep
  positivity

lemma liuAlphaGridPoint_eq_step {n i : ℕ} (hn : 0 < n) :
    liuAlphaGridPoint n i = 1 / 10 + (i : ℝ) * liuAlphaGridStep n := by
  unfold liuAlphaGridPoint liuAlphaGridStep
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

lemma liuBetaGridPoint_eq_step {n i : ℕ} (hn : 0 < n) :
    liuBetaGridPoint n i = 1 / 3 + (i : ℝ) * liuBetaGridStep n := by
  unfold liuBetaGridPoint liuBetaGridStep
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

lemma liuAlphaGridPoint_succ {n i : ℕ} (hn : 0 < n) :
    liuAlphaGridPoint n (i + 1) =
      liuAlphaGridPoint n i + liuAlphaGridStep n := by
  rw [liuAlphaGridPoint_eq_step hn, liuAlphaGridPoint_eq_step hn]
  push_cast
  ring

lemma liuBetaGridPoint_succ {n i : ℕ} (hn : 0 < n) :
    liuBetaGridPoint n (i + 1) =
      liuBetaGridPoint n i + liuBetaGridStep n := by
  rw [liuBetaGridPoint_eq_step hn, liuBetaGridPoint_eq_step hn]
  push_cast
  ring

lemma liuAlphaGridPoint_pos {n i : ℕ} (hn : 0 < n) :
    0 < liuAlphaGridPoint n i := by
  rw [liuAlphaGridPoint_eq_step hn]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hs := (liuAlphaGridStep_pos hn).le
  nlinarith [mul_nonneg hi hs]

lemma liuBetaGridPoint_pos {n i : ℕ} (hn : 0 < n) :
    0 < liuBetaGridPoint n i := by
  rw [liuBetaGridPoint_eq_step hn]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hs := (liuBetaGridStep_pos hn).le
  nlinarith [mul_nonneg hi hs]

lemma liuAlphaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    liuAlphaGridPoint n i < liuAlphaGridPoint n (i + 1) := by
  rw [liuAlphaGridPoint_succ hn]
  exact lt_add_of_pos_right _ (liuAlphaGridStep_pos hn)

lemma liuBetaGridPoint_lt_succ {n i : ℕ} (hn : 0 < n) :
    liuBetaGridPoint n i < liuBetaGridPoint n (i + 1) := by
  rw [liuBetaGridPoint_succ hn]
  exact lt_add_of_pos_right _ (liuBetaGridStep_pos hn)

lemma liuAlphaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    liuAlphaGridPoint n (i + 1) ≤ 1 / 3 := by
  have hin : ((i + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ((i + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 :=
    (div_le_one hnreal).mpr hin
  unfold liuAlphaGridPoint
  nlinarith

lemma liuAlphaGridStep_le {n : ℕ} (hn : 0 < n) :
    liuAlphaGridStep n ≤ 7 / 30 := by
  unfold liuAlphaGridStep
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_self (by norm_num) hnreal

/-- Natural ceilings give the unique endpoint convention needed by the grid:
strict on the left and non-strict on the right. -/
lemma exists_nat_cell (n : ℕ) {x a d : ℝ}
    (hd : 0 < d) (hx : a < x) (hxu : x ≤ a + (n : ℝ) * d) :
    ∃ i : ℕ, i < n ∧ a + (i : ℝ) * d < x ∧
      x ≤ a + ((i + 1 : ℕ) : ℝ) * d := by
  let t : ℝ := (x - a) / d
  let k : ℕ := Nat.ceil t
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.mpr hx) hd
  have htupper : t ≤ (n : ℝ) := by
    dsimp [t]
    rw [div_le_iff₀ hd]
    linarith
  have hkpos : 0 < k := Nat.ceil_pos.mpr htpos
  have hkle : k ≤ n := Nat.ceil_le.mpr htupper
  have hkcell : ((k - 1 : ℕ) : ℝ) < t ∧ t ≤ (k : ℝ) :=
    (Nat.ceil_eq_iff (Nat.ne_of_gt hkpos)).mp rfl
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · dsimp [t] at hkcell
    rw [lt_div_iff₀ hd] at hkcell
    linarith
  · dsimp [t] at hkcell
    rw [div_le_iff₀ hd] at hkcell
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    linarith

/-- The exact root-free source condition `p₁ p₂² ≤ N` becomes the triangular
inequality `α + 2β ≤ 1` in logarithmic coordinates. -/
theorem primeLogExponent_add_two_mul_le_one
    {N : ℕ} (hN : 8 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    primeLogExponent N p.1 + 2 * primeLogExponent N p.2 ≤ 1 := by
  have hc := mem_liuWeightPairs.mp hp
  have hp₁pos : (0 : ℝ) < p.1 := by exact_mod_cast hc.1.pos
  have hp₂pos : (0 : ℝ) < p.2 := by exact_mod_cast hc.2.1.pos
  have hsize : (p.1 : ℝ) * (p.2 : ℝ) ^ 2 ≤ N := by
    exact_mod_cast hc.2.2.2.2.2
  have hlog : Real.log ((p.1 : ℝ) * (p.2 : ℝ) ^ 2) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (mul_pos hp₁pos (pow_pos hp₂pos 2)) hsize
  rw [Real.log_mul (ne_of_gt hp₁pos) (pow_ne_zero 2 (ne_of_gt hp₂pos)),
    Real.log_pow] at hlog
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold primeLogExponent
  calc
    Real.log ↑p.1 / Real.log ↑N + 2 * (Real.log ↑p.2 / Real.log ↑N) =
        (Real.log ↑p.1 + 2 * Real.log ↑p.2) / Real.log ↑N := by ring
    _ ≤ 1 := (div_le_one hlogN).mpr (by norm_num at hlog ⊢; exact hlog)

/-- Every selected cell has its upper-right corner strictly below the kernel
singularity `α + β = 1`. -/
theorem liuLogGridCell_upperCorner_lt_one
    {n : ℕ} (hn : 0 < n) {q : Fin n × Fin n}
    (hq : q ∈ liuLogGridCells n) :
    liuAlphaGridPoint n (q.1 + 1) + liuBetaGridPoint n (q.2 + 1) < 1 := by
  rw [liuLogGridCells, Finset.mem_filter] at hq
  have hselected := hq.2
  have hαend := liuAlphaGridPoint_succ_le_end hn q.1.isLt
  have hstep := liuAlphaGridStep_le hn
  have hβstep : liuBetaGridStep n = liuAlphaGridStep n / 2 := by
    unfold liuAlphaGridStep liuBetaGridStep
    ring
  rw [liuAlphaGridPoint_succ hn] at hαend
  rw [liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn, hβstep]
  nlinarith

/-- Every Liu source pair belongs to a selected canonical cell.  The natural
ceiling construction handles points on upper grid boundaries without changing
the source's strict-lower/non-strict-upper convention. -/
theorem liuWeightPairs_covered_by_logGrid
    (n N : ℕ) (hn : 0 < n) (hN : 8 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    ∃ q ∈ liuLogGridCells n,
      LiuPairInLogRectangle N
        (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1))
        (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1)) p := by
  have hc := mem_liuWeightPairs.mp hp
  have hN1 : 1 < N := by omega
  have hsource := liuWeightPairs_source_range hp
  have hα := (primeLogExponent_mem_interval_iff hN1 hc.1.pos
    (1 / 10) (1 / 3)).mpr ⟨hsource.1, hsource.2.1⟩
  have hβ := (primeLogExponent_mem_interval_iff hN1 hc.2.1.pos
    (1 / 3) (9 / 20)).mpr ⟨hsource.2.2.1, hsource.2.2.2⟩
  have hαend :
      primeLogExponent N p.1 ≤ 1 / 10 + (n : ℝ) * liuAlphaGridStep n := by
    rw [show 1 / 10 + (n : ℝ) * liuAlphaGridStep n = (1 / 3 : ℝ) by
      unfold liuAlphaGridStep
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    exact hα.2
  have hβend :
      primeLogExponent N p.2 ≤ 1 / 3 + (n : ℝ) * liuBetaGridStep n := by
    rw [show 1 / 3 + (n : ℝ) * liuBetaGridStep n = (9 / 20 : ℝ) by
      unfold liuBetaGridStep
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    exact hβ.2
  obtain ⟨i, hi, hαlower, hαupper⟩ :=
    exists_nat_cell n (liuAlphaGridStep_pos hn) hα.1 hαend
  obtain ⟨j, hj, hβlower, hβupper⟩ :=
    exists_nat_cell n (liuBetaGridStep_pos hn) hβ.1 hβend
  let fi : Fin n := ⟨i, hi⟩
  let fj : Fin n := ⟨j, hj⟩
  have hαlower' : liuAlphaGridPoint n fi < primeLogExponent N p.1 := by
    simpa [fi, liuAlphaGridPoint_eq_step hn] using hαlower
  have hαupper' : primeLogExponent N p.1 ≤ liuAlphaGridPoint n (fi + 1) := by
    simpa [fi, liuAlphaGridPoint_eq_step hn] using hαupper
  have hβlower' : liuBetaGridPoint n fj < primeLogExponent N p.2 := by
    simpa [fj, liuBetaGridPoint_eq_step hn] using hβlower
  have hβupper' : primeLogExponent N p.2 ≤ liuBetaGridPoint n (fj + 1) := by
    simpa [fj, liuBetaGridPoint_eq_step hn] using hβupper
  have hselected :
      liuBetaGridPoint n fj < (1 - liuAlphaGridPoint n fi) / 2 := by
    nlinarith [primeLogExponent_add_two_mul_le_one hN hp]
  refine ⟨(fi, fj), ?_, ?_⟩
  · rw [liuLogGridCells, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hselected⟩
  · exact ⟨hαlower', hαupper', hβlower', hβupper'⟩

/-- The canonical selected grid majorizes the full finite Liu logarithmic
kernel sum. -/
theorem liuPairLogKernelSum_le_logGridMajorant
    (n N : ℕ) (hn : 0 < n) (hN : 8 ≤ N) :
    liuPairLogKernelSum N ≤ liuLogGridMajorant n N := by
  classical
  unfold liuLogGridMajorant
  exact liuPairLogKernelSum_le_sum_rectangleMajorants_of_cover
    (liuLogGridCells n)
    (fun q => liuAlphaGridPoint n q.1)
    (fun q => liuAlphaGridPoint n (q.1 + 1))
    (fun q => liuBetaGridPoint n q.2)
    (fun q => liuBetaGridPoint n (q.2 + 1))
    N hN
    (fun q _ => liuAlphaGridPoint_pos hn)
    (fun q _ => liuAlphaGridPoint_lt_succ hn)
    (fun q _ => liuBetaGridPoint_pos hn)
    (fun q _ => liuBetaGridPoint_lt_succ hn)
    (fun q hq => liuLogGridCell_upperCorner_lt_one hn hq)
    (fun p hp => liuWeightPairs_covered_by_logGrid n N hn hN hp)

/-- For every fixed positive grid size, the finite-`N` majorant tends to its
logarithmic upper sum. -/
theorem tendsto_liuLogGridMajorant
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => liuLogGridMajorant n N) atTop
      (nhds (liuLogGridUpperSum n)) := by
  classical
  unfold liuLogGridMajorant liuLogGridUpperSum
  exact tendsto_weighted_sum_primeReciprocalLogRectangle
    (liuLogGridCells n)
    (fun q => 1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1)))
    (fun q => liuAlphaGridPoint n q.1)
    (fun q => liuAlphaGridPoint n (q.1 + 1))
    (fun q => liuBetaGridPoint n q.2)
    (fun q => liuBetaGridPoint n (q.2 + 1))
    (fun q _ => liuAlphaGridPoint_pos hn)
    (fun q _ => liuAlphaGridPoint_lt_succ hn)
    (fun q _ => liuBetaGridPoint_pos hn)
    (fun q _ => liuBetaGridPoint_lt_succ hn)

/-- Eventual epsilon form of fixed canonical-grid convergence. -/
theorem eventually_abs_liuLogGridMajorant_sub_lt
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |liuLogGridMajorant n N - liuLogGridUpperSum n| < ε := by
  have h := tendsto_liuLogGridMajorant n hn
  rw [Metric.tendsto_nhds] at h
  filter_upwards [h ε hε] with N hN
  simpa only [Real.dist_eq] using hN

/-- Threshold form of fixed canonical-grid convergence. -/
theorem exists_abs_liuLogGridMajorant_sub_lt
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |liuLogGridMajorant n N - liuLogGridUpperSum n| < ε := by
  simpa only [eventually_atTop] using
    eventually_abs_liuLogGridMajorant_sub_lt n hn hε

end MathlibNt.SieveTheory.LiuWeight
