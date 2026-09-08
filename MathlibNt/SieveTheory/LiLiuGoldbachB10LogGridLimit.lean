import MathlibNt.Analysis.IntegralExcessCover
import MathlibNt.SieveTheory.LiLiuGoldbachB10LogGrid
import MathlibNt.SieveTheory.LiuPrimePairLogGridLimit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Filter Finset MeasureTheory Set
open scoped ENNReal BigOperators Interval Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

set_option maxHeartbeats 800000

open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

private abbrev goldbachB10LogDensity : ℝ × ℝ → ℝ := liuLogDensity
private abbrev goldbachB10LogKernel : ℝ × ℝ → ℝ := liuLogKernel
private abbrev goldbachB10LogIntegrand : ℝ × ℝ → ℝ := liuLogIntegrand

/-- The actual two-variable integral `I10` from Liu's printed `(5.46)`. -/
noncomputable def goldbachB10MainIntegral : ℝ :=
  ∫ u in goldbachB10Beta..goldbachB10Gamma,
    ∫ v in goldbachB10Gamma..((1 - u) / 2),
      1 / (u * v * (1 - u - v))

private def goldbachB10LogGridCell (n : ℕ) (q : Fin n × Fin n) : Set (ℝ × ℝ) :=
  Ioc (goldbachB10AlphaGridPoint n q.1) (goldbachB10AlphaGridPoint n (q.1 + 1)) ×ˢ
    Ioc (goldbachB10BetaGridPoint n q.2) (goldbachB10BetaGridPoint n (q.2 + 1))

private def goldbachB10LogGridRegion (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ goldbachB10LogGridCells n, goldbachB10LogGridCell n q

private def goldbachB10LogSourceRegion : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc goldbachB10Beta goldbachB10Gamma ∧
    x.2 ∈ Ioc goldbachB10Gamma ((1 - x.1) / 2)}

private def goldbachB10LogAmbientBox : Set (ℝ × ℝ) :=
  Icc goldbachB10AlphaGridStart goldbachB10Gamma ×ˢ
    Icc goldbachB10BetaGridStart goldbachB10BetaGridEnd

private def goldbachB10LogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ goldbachB10LogGridCells n,
    (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1))) *
      (goldbachB10LogGridCell n q).indicator goldbachB10LogDensity x

private def goldbachB10LeftStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Ioc (goldbachB10Beta - goldbachB10AlphaGridStep n) goldbachB10Beta ×ˢ
    Icc goldbachB10BetaGridStart goldbachB10BetaGridEnd

private def goldbachB10BottomStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Icc goldbachB10Beta goldbachB10Gamma ×ˢ
    Ioc (goldbachB10Gamma - goldbachB10BetaGridStep n) goldbachB10Gamma

private def goldbachB10ObliqueStrip (n : ℕ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc goldbachB10Beta goldbachB10Gamma ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 +
      (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2}

private lemma goldbachB10Beta_le_gamma : goldbachB10Beta ≤ goldbachB10Gamma := by
  dsimp [goldbachB10Beta, goldbachB10Gamma]
  norm_num

private lemma goldbachB10Gamma_le_half : goldbachB10Gamma ≤ (1 / 2 : ℝ) := by
  dsimp [goldbachB10Gamma]
  norm_num

private lemma goldbachB10Gamma_le_half_minus_beta : goldbachB10Gamma ≤ (1 - goldbachB10Beta) / 2 := by
  dsimp [goldbachB10Gamma, goldbachB10Beta]
  norm_num

private lemma goldbachB10BetaGridEnd_eq_half_minus_beta :
    goldbachB10BetaGridEnd = (1 - goldbachB10Beta) / 2 := by
  dsimp [goldbachB10BetaGridEnd, goldbachB10Beta]
  ring

private lemma measurableSet_goldbachB10LogGridCell (n : ℕ) (q : Fin n × Fin n) :
    MeasurableSet (goldbachB10LogGridCell n q) :=
  measurableSet_Ioc.prod measurableSet_Ioc

private theorem goldbachB10LogGridCell_pairwiseDisjoint {n : ℕ} (hn : 0 < n) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (goldbachB10LogGridCell n)) := by
  intro q hq r hr hqr
  change Disjoint (goldbachB10LogGridCell n q) (goldbachB10LogGridCell n r)
  rw [Set.disjoint_left]
  intro x hxq hxr
  change
    x.1 ∈ Ioc (goldbachB10AlphaGridPoint n q.1) (goldbachB10AlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB10BetaGridPoint n q.2) (goldbachB10BetaGridPoint n (q.2 + 1))
    at hxq
  change
    x.1 ∈ Ioc (goldbachB10AlphaGridPoint n r.1) (goldbachB10AlphaGridPoint n (r.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB10BetaGridPoint n r.2) (goldbachB10BetaGridPoint n (r.2 + 1))
    at hxr
  rcases hxq with ⟨hqa, hqb⟩
  rcases hxr with ⟨hra, hrb⟩
  by_cases hi : q.1 = r.1
  · have hj : q.2 ≠ r.2 := by
      intro h
      apply hqr
      exact Prod.ext hi h
    rcases lt_or_gt_of_ne hj with hjlt | hjgt
    · have hle := goldbachB10BetaGridPoint_mono hn
        (show (q.2 : ℕ) + 1 ≤ (r.2 : ℕ) by omega)
      exact not_lt_of_ge hle (hrb.1.trans_le hqb.2)
    · have hle := goldbachB10BetaGridPoint_mono hn
        (show (r.2 : ℕ) + 1 ≤ (q.2 : ℕ) by omega)
      exact not_lt_of_ge hle (hqb.1.trans_le hrb.2)
  · rcases lt_or_gt_of_ne hi with hilt | higt
    · have hle := goldbachB10AlphaGridPoint_mono hn
        (show (q.1 : ℕ) + 1 ≤ (r.1 : ℕ) by omega)
      exact not_lt_of_ge hle (hra.1.trans_le hqa.2)
    · have hle := goldbachB10AlphaGridPoint_mono hn
        (show (r.1 : ℕ) + 1 ≤ (q.1 : ℕ) by omega)
      exact not_lt_of_ge hle (hqa.1.trans_le hra.2)

private theorem goldbachB10LogSourceRegion_subset_gridRegion {n : ℕ} (hn : 0 < n) :
    goldbachB10LogSourceRegion ⊆ goldbachB10LogGridRegion n := by
  intro x hx
  have hαstart : goldbachB10AlphaGridStart < x.1 := by
    exact lt_trans (by
      dsimp [goldbachB10AlphaGridStart, goldbachB10Beta]
      norm_num) hx.1.1
  have hβstart : goldbachB10BetaGridStart < x.2 := by
    exact lt_trans (by
      dsimp [goldbachB10BetaGridStart, goldbachB10Gamma]
      norm_num) hx.2.1
  have hαend :
      x.1 ≤ goldbachB10AlphaGridStart + (n : ℝ) * goldbachB10AlphaGridStep n := by
    rw [show goldbachB10AlphaGridStart + (n : ℝ) * goldbachB10AlphaGridStep n =
        goldbachB10Gamma by
      unfold goldbachB10AlphaGridStart goldbachB10AlphaGridStep goldbachB10AlphaGridWidth
      dsimp [goldbachB10Gamma]
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    exact hx.1.2
  have hβend :
      x.2 ≤ goldbachB10BetaGridStart + (n : ℝ) * goldbachB10BetaGridStep n := by
    rw [show goldbachB10BetaGridStart + (n : ℝ) * goldbachB10BetaGridStep n =
        goldbachB10BetaGridEnd by
      unfold goldbachB10BetaGridStart goldbachB10BetaGridStep goldbachB10BetaGridWidth
        goldbachB10BetaGridEnd
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    rw [goldbachB10BetaGridEnd_eq_half_minus_beta]
    exact le_trans hx.2.2 (by gcongr; exact hx.1.1.le)
  obtain ⟨i, hi, hail, haiu⟩ :=
    exists_nat_cell n (goldbachB10AlphaGridStep_pos hn) hαstart hαend
  obtain ⟨j, hj, hbjl, hbju⟩ :=
    exists_nat_cell n (goldbachB10BetaGridStep_pos hn) hβstart hβend
  let fi : Fin n := ⟨i, hi⟩
  let fj : Fin n := ⟨j, hj⟩
  have hselected :
      goldbachB10Beta ≤ goldbachB10AlphaGridPoint n (fi + 1) ∧
        goldbachB10Gamma ≤ goldbachB10BetaGridPoint n (fj + 1) ∧
        goldbachB10AlphaGridPoint n fi + 2 * goldbachB10BetaGridPoint n fj < 1 := by
    constructor
    · have hright : x.1 ≤ goldbachB10AlphaGridPoint n (fi + 1) := by
        simpa [fi, goldbachB10AlphaGridPoint_eq_step hn] using haiu
      exact hx.1.1.le.trans hright
    constructor
    · have htop : x.2 ≤ goldbachB10BetaGridPoint n (fj + 1) := by
        simpa [fj, goldbachB10BetaGridPoint_eq_step hn] using hbju
      exact hx.2.1.le.trans htop
    · have hleft : goldbachB10AlphaGridPoint n fi < x.1 := by
        simpa [fi, goldbachB10AlphaGridPoint_eq_step hn] using hail
      have hlow : goldbachB10BetaGridPoint n fj < x.2 := by
        simpa [fj, goldbachB10BetaGridPoint_eq_step hn] using hbjl
      linarith [hx.2.2]
  rw [goldbachB10LogGridRegion]
  refine Set.mem_iUnion.2 ⟨(fi, fj), Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · rw [goldbachB10LogGridCells, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hselected.1, hselected.2.1, hselected.2.2⟩
  · exact ⟨⟨by simpa [fi, goldbachB10AlphaGridPoint_eq_step hn] using hail,
        by simpa [fi, goldbachB10AlphaGridPoint_eq_step hn] using haiu⟩,
      ⟨by simpa [fj, goldbachB10BetaGridPoint_eq_step hn] using hbjl,
        by simpa [fj, goldbachB10BetaGridPoint_eq_step hn] using hbju⟩⟩

private theorem goldbachB10LogGridRegion_geometry {n : ℕ} (hn : 0 < n) {x : ℝ × ℝ}
    (hx : x ∈ goldbachB10LogGridRegion n) :
    x.1 ∈ Ioc goldbachB10AlphaGridStart goldbachB10Gamma ∧
      x.2 ∈ Ioc goldbachB10BetaGridStart goldbachB10BetaGridEnd ∧
      x.1 + 2 * x.2 <
        1 + (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) := by
  rw [goldbachB10LogGridRegion] at hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨hq, hxcell⟩ := Set.mem_iUnion.1 hx
  have hcorner :
      goldbachB10AlphaGridPoint n q.1 + 2 * goldbachB10BetaGridPoint n q.2 < 1 := by
    rw [goldbachB10LogGridCells, Finset.mem_filter] at hq
    exact hq.2.2.2
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have h0 : goldbachB10AlphaGridStart ≤ goldbachB10AlphaGridPoint n q.1 := by
      rw [goldbachB10AlphaGridPoint_eq_step hn]
      exact le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg _) (goldbachB10AlphaGridStep_pos hn).le)
    exact h0.trans_lt hxcell.1.1
  · exact hxcell.1.2.trans (goldbachB10AlphaGridPoint_succ_le_end hn q.1.isLt)
  · have h0 : goldbachB10BetaGridStart ≤ goldbachB10BetaGridPoint n q.2 := by
      rw [goldbachB10BetaGridPoint_eq_step hn]
      exact le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg _) (goldbachB10BetaGridStep_pos hn).le)
    exact h0.trans_lt hxcell.2.1
  · exact hxcell.2.2.trans (goldbachB10BetaGridPoint_succ_le_end hn q.2.isLt)
  · have hxcell' :
        x.1 ∈ Ioc (goldbachB10AlphaGridPoint n q.1)
            (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) ∧
          x.2 ∈ Ioc (goldbachB10BetaGridPoint n q.2)
            (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) := by
      simpa [goldbachB10LogGridCell, goldbachB10AlphaGridPoint_succ hn,
        goldbachB10BetaGridPoint_succ hn] using hxcell
    linarith [hxcell'.1.2, hxcell'.2.2, hcorner]

private theorem goldbachB10LogSourceRegion_subset_ambientBox :
    goldbachB10LogSourceRegion ⊆ goldbachB10LogAmbientBox := by
  intro x hx
  refine ⟨⟨?_, hx.1.2⟩, ⟨?_, ?_⟩⟩
  · exact le_trans (by
      dsimp [goldbachB10AlphaGridStart, goldbachB10Beta]
      norm_num : goldbachB10AlphaGridStart ≤ goldbachB10Beta) hx.1.1.le
  · exact le_trans (by
      dsimp [goldbachB10BetaGridStart, goldbachB10Gamma]
      norm_num : goldbachB10BetaGridStart ≤ goldbachB10Gamma) hx.2.1.le
  · rw [goldbachB10BetaGridEnd_eq_half_minus_beta]
    exact le_trans hx.2.2 (by gcongr; exact hx.1.1.le)

private theorem goldbachB10LogGridRegion_subset_ambientBox {n : ℕ} (hn : 0 < n) :
    goldbachB10LogGridRegion n ⊆ goldbachB10LogAmbientBox := by
  intro x hx
  exact ⟨⟨(goldbachB10LogGridRegion_geometry hn hx).1.1.le,
      (goldbachB10LogGridRegion_geometry hn hx).1.2⟩,
    ⟨(goldbachB10LogGridRegion_geometry hn hx).2.1.1.le,
      (goldbachB10LogGridRegion_geometry hn hx).2.1.2⟩⟩

private lemma measurableSet_goldbachB10LogGridRegion (n : ℕ) :
    MeasurableSet (goldbachB10LogGridRegion n) := by
  classical
  rw [goldbachB10LogGridRegion]
  exact Finset.measurableSet_biUnion _ fun q _ => measurableSet_goldbachB10LogGridCell n q

private lemma measurableSet_goldbachB10LogSourceRegion :
    MeasurableSet goldbachB10LogSourceRegion := by
  change MeasurableSet
    {x : ℝ × ℝ | x.1 ∈ Ioc goldbachB10Beta goldbachB10Gamma ∧
      x.2 ∈ Ioc goldbachB10Gamma ((1 - x.1) / 2)}
  have hset :
      {x : ℝ × ℝ | x.1 ∈ Ioc goldbachB10Beta goldbachB10Gamma ∧
        x.2 ∈ Ioc goldbachB10Gamma ((1 - x.1) / 2)} =
      Prod.fst ⁻¹' Ioc goldbachB10Beta goldbachB10Gamma ∩
        (Prod.snd ⁻¹' Ioi goldbachB10Gamma ∩
          {x : ℝ × ℝ | x.2 ≤ (1 - x.1) / 2}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioc, Set.mem_Ioi]
  rw [hset]
  exact (measurable_fst measurableSet_Ioc).inter
    ((measurable_snd measurableSet_Ioi).inter
      (measurableSet_le measurable_snd (by fun_prop)))

private lemma measurableSet_goldbachB10LogAmbientBox :
    MeasurableSet goldbachB10LogAmbientBox :=
  measurableSet_Icc.prod measurableSet_Icc

private lemma isCompact_goldbachB10LogAmbientBox :
    IsCompact goldbachB10LogAmbientBox :=
  isCompact_Icc.prod isCompact_Icc

private lemma goldbachB10LogDensity_nonneg {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogAmbientBox) :
    0 ≤ goldbachB10LogDensity x := by
  dsimp [goldbachB10LogAmbientBox, goldbachB10LogDensity, liuLogDensity]
  have hx1 : 0 ≤ x.1 := by
    exact le_trans (by
      dsimp [goldbachB10AlphaGridStart]
      norm_num : (0 : ℝ) ≤ goldbachB10AlphaGridStart) hx.1.1
  have hx2 : 0 ≤ x.2 := by
    exact le_trans (by
      dsimp [goldbachB10BetaGridStart]
      norm_num : (0 : ℝ) ≤ goldbachB10BetaGridStart) hx.2.1
  apply one_div_nonneg.mpr
  exact mul_nonneg hx1 hx2

private lemma goldbachB10LogKernel_nonneg {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogAmbientBox) :
    0 ≤ goldbachB10LogKernel x := by
  dsimp [goldbachB10LogAmbientBox, goldbachB10LogKernel, liuLogKernel]
  apply one_div_nonneg.mpr
  have hden : 0 ≤ 1 - x.1 - x.2 := by
    have hsum : x.1 + x.2 ≤ goldbachB10Gamma + goldbachB10BetaGridEnd := by
      exact add_le_add hx.1.2 hx.2.2
    dsimp [goldbachB10Gamma, goldbachB10BetaGridEnd] at hsum ⊢
    linarith
  exact hden

private lemma goldbachB10LogIntegrand_nonneg {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogAmbientBox) :
    0 ≤ goldbachB10LogIntegrand x := by
  dsimp [goldbachB10LogIntegrand, liuLogIntegrand]
  exact mul_nonneg (goldbachB10LogKernel_nonneg hx) (goldbachB10LogDensity_nonneg hx)

private lemma continuousOn_goldbachB10LogDensity :
    ContinuousOn goldbachB10LogDensity goldbachB10LogAmbientBox := by
  unfold goldbachB10LogDensity liuLogDensity
  apply ContinuousOn.div continuousOn_const
    (continuous_fst.continuousOn.mul continuous_snd.continuousOn)
  intro x hx
  exact mul_ne_zero (by
      have : (0 : ℝ) < goldbachB10AlphaGridStart := by
        dsimp [goldbachB10AlphaGridStart]
        norm_num
      linarith [hx.1.1])
    (by
      have : (0 : ℝ) < goldbachB10BetaGridStart := by
        dsimp [goldbachB10BetaGridStart]
        norm_num
      linarith [hx.2.1])

private lemma continuousOn_goldbachB10LogKernel :
    ContinuousOn goldbachB10LogKernel goldbachB10LogAmbientBox := by
  unfold goldbachB10LogKernel liuLogKernel
  apply ContinuousOn.div continuousOn_const
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn)
  intro x hx
  change 1 - x.1 - x.2 ≠ 0
  have hsum : x.1 + x.2 ≤ goldbachB10Gamma + goldbachB10BetaGridEnd := by
    exact add_le_add hx.1.2 hx.2.2
  dsimp [goldbachB10Gamma, goldbachB10BetaGridEnd] at hsum ⊢
  linarith

private lemma continuousOn_goldbachB10LogIntegrand :
    ContinuousOn goldbachB10LogIntegrand goldbachB10LogAmbientBox := by
  exact continuousOn_goldbachB10LogKernel.mul continuousOn_goldbachB10LogDensity

private lemma integrableOn_goldbachB10LogDensity {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB10LogAmbientBox) :
    IntegrableOn goldbachB10LogDensity s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_goldbachB10LogDensity
    isCompact_goldbachB10LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB10LogAmbientBox.measure_lt_top).ne

private lemma integrableOn_goldbachB10LogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB10LogAmbientBox) :
    IntegrableOn goldbachB10LogIntegrand s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_goldbachB10LogIntegrand
    isCompact_goldbachB10LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB10LogAmbientBox.measure_lt_top).ne

private lemma goldbachB10MainIntegral_eq_iteratedSetIntegral :
    goldbachB10MainIntegral =
      ∫ u in Ioc goldbachB10Beta goldbachB10Gamma,
        ∫ v in Ioc goldbachB10Gamma ((1 - u) / 2),
          goldbachB10LogIntegrand (u, v) := by
  unfold goldbachB10MainIntegral
  rw [intervalIntegral.integral_of_le goldbachB10Beta_le_gamma]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hu' : u ∈ Icc goldbachB10Beta goldbachB10Gamma := ⟨hu.1.le, hu.2⟩
  have hle : goldbachB10Gamma ≤ (1 - u) / 2 := by
    have huγ : u ≤ (3 / 11 : ℝ) := by simpa [goldbachB10Gamma] using hu'.2
    dsimp [goldbachB10Gamma]
    linarith
  change (∫ v in goldbachB10Gamma..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      ∫ v in Ioc goldbachB10Gamma ((1 - u) / 2), goldbachB10LogIntegrand (u, v)
  rw [intervalIntegral.integral_of_le hle]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  have hv' : v ∈ Icc goldbachB10Gamma ((1 - u) / 2) := ⟨hv.1.le, hv.2⟩
  have hu0 : u ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by
      dsimp [goldbachB10Beta]
      norm_num) hu'.1)
  have hv0 : v ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by
      dsimp [goldbachB10Gamma]
      norm_num) hv'.1)
  have hhalfPos : 0 < (1 - u) / 2 := by
    have huOne : u < (1 : ℝ) := lt_of_le_of_lt hu'.2 (by
      dsimp [goldbachB10Gamma]
      norm_num)
    linarith
  have hden : 1 - u - v ≠ 0 := by
    have hpos : 0 < 1 - u - v := by
      nlinarith [hv'.2, hhalfPos]
    exact ne_of_gt hpos
  change 1 / (u * v * (1 - u - v)) = liuLogIntegrand (u, v)
  unfold liuLogIntegrand liuLogKernel liuLogDensity
  field_simp [hu0, hv0, hden]

/-- The actual B10 main integral is the set integral of the logarithmic kernel
over the exact half-open source triangle. -/
theorem goldbachB10MainIntegral_eq_setIntegral :
    goldbachB10MainIntegral =
      ∫ x in goldbachB10LogSourceRegion, goldbachB10LogIntegrand x := by
  rw [goldbachB10MainIntegral_eq_iteratedSetIntegral]
  let F : ℝ × ℝ → ℝ := goldbachB10LogSourceRegion.indicator goldbachB10LogIntegrand
  have hF : Integrable F := by
    refine (integrableOn_iff_integrable_of_support_subset
      (μ := volume) (f := F) (s := goldbachB10LogSourceRegion) ?_).mp ?_
    · intro x hx
      by_contra hxs
      exact (Function.mem_support.1 hx) (by simp [F, hxs])
    · apply (integrableOn_goldbachB10LogIntegrand measurableSet_goldbachB10LogSourceRegion
        goldbachB10LogSourceRegion_subset_ambientBox).congr_fun
      · intro x hx
        simp [F, hx]
      · exact measurableSet_goldbachB10LogSourceRegion
  have hinner (u : ℝ) :
      (∫ v, F (u, v)) =
        (Ioc goldbachB10Beta goldbachB10Gamma).indicator
          (fun u => ∫ v in Ioc goldbachB10Gamma ((1 - u) / 2),
            goldbachB10LogIntegrand (u, v)) u := by
    by_cases hu : u ∈ Ioc goldbachB10Beta goldbachB10Gamma
    · rw [Set.indicator_of_mem hu, ← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with v
      have hmem : (u, v) ∈ goldbachB10LogSourceRegion ↔
          v ∈ Ioc goldbachB10Gamma ((1 - u) / 2) := by
        change (u ∈ Ioc goldbachB10Beta goldbachB10Gamma ∧
          v ∈ Ioc goldbachB10Gamma ((1 - u) / 2)) ↔ _
        exact and_iff_right hu
      change goldbachB10LogSourceRegion.indicator goldbachB10LogIntegrand (u, v) =
        (Ioc goldbachB10Gamma ((1 - u) / 2)).indicator
          (fun v => goldbachB10LogIntegrand (u, v)) v
      by_cases hv : v ∈ Ioc goldbachB10Gamma ((1 - u) / 2)
      · rw [Set.indicator_of_mem (hmem.mpr hv), Set.indicator_of_mem hv]
      · rw [Set.indicator_of_notMem (fun h => hv (hmem.mp h)),
          Set.indicator_of_notMem hv]
    · rw [Set.indicator_of_notMem hu]
      apply integral_eq_zero_of_ae
      filter_upwards with v
      have hnot : (u, v) ∉ goldbachB10LogSourceRegion := by
        intro h
        exact hu h.1
      change goldbachB10LogSourceRegion.indicator goldbachB10LogIntegrand (u, v) = 0
      rw [Set.indicator_of_notMem hnot]
  have hFubini :
      (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact MeasureTheory.integral_prod F hF
  calc
    (∫ u in Ioc goldbachB10Beta goldbachB10Gamma,
        ∫ v in Ioc goldbachB10Gamma ((1 - u) / 2),
          goldbachB10LogIntegrand (u, v)) =
        ∫ u, (Ioc goldbachB10Beta goldbachB10Gamma).indicator
          (fun u => ∫ v in Ioc goldbachB10Gamma ((1 - u) / 2),
            goldbachB10LogIntegrand (u, v)) u := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ u, ∫ v, F (u, v) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (hinner u).symm
    _ = ∫ z, F z := hFubini.symm
    _ = ∫ x in goldbachB10LogSourceRegion, goldbachB10LogIntegrand x := by
      rw [MeasureTheory.integral_indicator measurableSet_goldbachB10LogSourceRegion]

private lemma goldbachB10LogGridCell_subset_ambientBox {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ goldbachB10LogGridCells n) :
    goldbachB10LogGridCell n q ⊆ goldbachB10LogAmbientBox := by
  intro x hx
  apply goldbachB10LogGridRegion_subset_ambientBox hn
  rw [goldbachB10LogGridRegion]
  exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hx⟩⟩

private theorem goldbachB10LogGridUpperSum_eq_integral (n : ℕ) (hn : 0 < n) :
    goldbachB10LogGridUpperSum n = ∫ x, goldbachB10LogGridUpperIntegrand n x := by
  classical
  unfold goldbachB10LogGridUpperSum goldbachB10LogGridUpperIntegrand
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator (measurableSet_goldbachB10LogGridCell n q)]
    rw [logarithmicRectangleMass_eq_setIntegral
      (goldbachB10AlphaGridPoint_pos hn) (goldbachB10AlphaGridPoint_lt_succ hn)
      (goldbachB10BetaGridPoint_pos hn) (goldbachB10BetaGridPoint_lt_succ hn)]
    rfl
  · intro q hq
    exact (integrable_indicator_of_integrableOn
      (measurableSet_goldbachB10LogGridCell n q)
      (integrableOn_goldbachB10LogDensity (measurableSet_goldbachB10LogGridCell n q)
        (goldbachB10LogGridCell_subset_ambientBox hn hq))).const_mul _

private lemma integrable_goldbachB10LogGridUpperIntegrand (n : ℕ) (hn : 0 < n) :
    Integrable (goldbachB10LogGridUpperIntegrand n) := by
  classical
  unfold goldbachB10LogGridUpperIntegrand
  exact integrable_finsetSum _ fun q hq =>
    (integrable_indicator_of_integrableOn
      (measurableSet_goldbachB10LogGridCell n q)
      (integrableOn_goldbachB10LogDensity (measurableSet_goldbachB10LogGridCell n q)
        (goldbachB10LogGridCell_subset_ambientBox hn hq))).const_mul _

private lemma goldbachB10LogGridUpperIntegrand_nonneg {n : ℕ} (hn : 0 < n)
    (x : ℝ × ℝ) : 0 ≤ goldbachB10LogGridUpperIntegrand n x := by
  classical
  unfold goldbachB10LogGridUpperIntegrand
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg
  · apply one_div_nonneg.mpr
    linarith [goldbachB10LogGridCell_upperCorner_lt_one hn hq]
  · by_cases hx : x ∈ goldbachB10LogGridCell n q
    · rw [Set.indicator_of_mem hx]
      exact goldbachB10LogDensity_nonneg (goldbachB10LogGridCell_subset_ambientBox hn hq hx)
    · rw [Set.indicator_of_notMem hx]

private lemma goldbachB10LogIntegrand_le_goldbachB10LogGridUpperIntegrand {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogSourceRegion) :
    goldbachB10LogIntegrand x ≤ goldbachB10LogGridUpperIntegrand n x := by
  classical
  have hxregion := goldbachB10LogSourceRegion_subset_gridRegion hn hx
  rw [goldbachB10LogGridRegion] at hxregion
  obtain ⟨q, hxregion⟩ := Set.mem_iUnion.1 hxregion
  obtain ⟨hq, hxq⟩ := Set.mem_iUnion.1 hxregion
  have hdenUpper : 0 < 1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1) := by
    linarith [goldbachB10LogGridCell_upperCorner_lt_one hn hq]
  have hden : 1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1) ≤ 1 - x.1 - x.2 := by
    linarith [hxq.1.2, hxq.2.2]
  have hkernel :
      goldbachB10LogKernel x ≤
        1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
          goldbachB10BetaGridPoint n (q.2 + 1)) := by
    unfold goldbachB10LogKernel liuLogKernel
    exact one_div_le_one_div_of_le hdenUpper hden
  have hdensity : 0 ≤ goldbachB10LogDensity x :=
    goldbachB10LogDensity_nonneg (goldbachB10LogGridCell_subset_ambientBox hn hq hxq)
  have hterm :
      goldbachB10LogIntegrand x ≤
        (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
          goldbachB10BetaGridPoint n (q.2 + 1))) *
          (goldbachB10LogGridCell n q).indicator goldbachB10LogDensity x := by
    rw [Set.indicator_of_mem hxq]
    unfold goldbachB10LogIntegrand liuLogIntegrand
    exact mul_le_mul_of_nonneg_right hkernel hdensity
  refine hterm.trans ?_
  unfold goldbachB10LogGridUpperIntegrand
  refine Finset.single_le_sum
    (f := fun r =>
      (1 / (1 - goldbachB10AlphaGridPoint n (r.1 + 1) -
        goldbachB10BetaGridPoint n (r.2 + 1))) *
        (goldbachB10LogGridCell n r).indicator goldbachB10LogDensity x)
    (fun r hr => by
      apply mul_nonneg
      · apply one_div_nonneg.mpr
        linarith [goldbachB10LogGridCell_upperCorner_lt_one hn hr]
      · by_cases hxr : x ∈ goldbachB10LogGridCell n r
        · rw [Set.indicator_of_mem hxr]
          exact goldbachB10LogDensity_nonneg (goldbachB10LogGridCell_subset_ambientBox hn hr hxr)
        · rw [Set.indicator_of_notMem hxr])
    hq

private theorem goldbachB10MainIntegral_le_goldbachB10LogGridUpperSum (n : ℕ) (hn : 0 < n) :
    goldbachB10MainIntegral ≤ goldbachB10LogGridUpperSum n := by
  have hsource : Integrable (goldbachB10LogSourceRegion.indicator goldbachB10LogIntegrand) :=
    integrable_indicator_of_integrableOn measurableSet_goldbachB10LogSourceRegion
      (integrableOn_goldbachB10LogIntegrand measurableSet_goldbachB10LogSourceRegion
        goldbachB10LogSourceRegion_subset_ambientBox)
  have hupper := integrable_goldbachB10LogGridUpperIntegrand n hn
  rw [goldbachB10MainIntegral_eq_setIntegral,
    goldbachB10LogGridUpperSum_eq_integral n hn,
    ← MeasureTheory.integral_indicator measurableSet_goldbachB10LogSourceRegion]
  apply MeasureTheory.integral_mono hsource hupper
  intro x
  by_cases hx : x ∈ goldbachB10LogSourceRegion
  · rw [Set.indicator_of_mem hx]
    exact goldbachB10LogIntegrand_le_goldbachB10LogGridUpperIntegrand hn hx
  · rw [Set.indicator_of_notMem hx]
    exact goldbachB10LogGridUpperIntegrand_nonneg hn x

private lemma volume_unitBox :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod]
  norm_num [Real.volume_Icc]

private lemma goldbachB10LogDensity_le_forty {x : ℝ × ℝ}
    (hx : x ∈ goldbachB10LogAmbientBox) :
    goldbachB10LogDensity x ≤ 40 := by
  have hprod : (1 / 40 : ℝ) ≤ x.1 * x.2 := by
    have h1 : (1 / 10 : ℝ) ≤ x.1 := by
      simpa [goldbachB10AlphaGridStart] using hx.1.1
    have h2 : (1 / 4 : ℝ) ≤ x.2 := by
      simpa [goldbachB10BetaGridStart] using hx.2.1
    calc
      (1 / 40 : ℝ) = (1 / 10 : ℝ) * (1 / 4 : ℝ) := by norm_num
      _ ≤ x.1 * x.2 := by gcongr
  unfold goldbachB10LogDensity liuLogDensity
  rw [div_le_iff₀ (by linarith [hx.1.1, hx.2.1])]
  nlinarith

private lemma goldbachB10LogGrid_upperKernel_le_four {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (_hq : q ∈ goldbachB10LogGridCells n) :
    1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1)) ≤ 4 := by
  have hα := goldbachB10AlphaGridPoint_succ_le_end hn q.1.isLt
  have hβ := goldbachB10BetaGridPoint_succ_le_end hn q.2.isLt
  have hden : (1 / 4 : ℝ) ≤
      1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
        goldbachB10BetaGridPoint n (q.2 + 1) := by
    dsimp [goldbachB10Gamma, goldbachB10BetaGridEnd] at hα hβ
    linarith
  rw [div_le_iff₀ (by linarith [hden])]
  nlinarith

private lemma goldbachB10LogGridUpperIntegrand_eq_of_mem {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ goldbachB10LogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogGridCell n q) :
    goldbachB10LogGridUpperIntegrand n x =
      (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
        goldbachB10BetaGridPoint n (q.2 + 1))) * goldbachB10LogDensity x := by
  classical
  unfold goldbachB10LogGridUpperIntegrand
  rw [Finset.sum_eq_single q]
  · rw [Set.indicator_of_mem hx]
  · intro r hr hrq
    have hnot : x ∉ goldbachB10LogGridCell n r := by
      intro hxr
      have hd : Disjoint (goldbachB10LogGridCell n q) (goldbachB10LogGridCell n r) :=
        goldbachB10LogGridCell_pairwiseDisjoint hn
          (Set.mem_univ q) (Set.mem_univ r) hrq.symm
      exact Set.disjoint_left.1 hd hx hxr
    rw [Set.indicator_of_notMem hnot, mul_zero]
  · exact fun h => (h hq).elim

private lemma goldbachB10LogGridUpperIntegrand_eq_zero_of_notMem {n : ℕ}
    {x : ℝ × ℝ} (hx : x ∉ goldbachB10LogGridRegion n) :
    goldbachB10LogGridUpperIntegrand n x = 0 := by
  classical
  unfold goldbachB10LogGridUpperIntegrand
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : x ∉ goldbachB10LogGridCell n q := by
    intro hxq
    apply hx
    rw [goldbachB10LogGridRegion]
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hxq⟩⟩
  rw [Set.indicator_of_notMem hnot, mul_zero]

private lemma goldbachB10LogGridUpperIntegrand_le_oneSixty {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogGridRegion n) :
    goldbachB10LogGridUpperIntegrand n x ≤ 160 := by
  rw [goldbachB10LogGridRegion] at hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx
  rw [goldbachB10LogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB10LogDensity_le_forty (goldbachB10LogGridCell_subset_ambientBox hn hq hxq)
  have hk := goldbachB10LogGrid_upperKernel_le_four hn hq
  have hd0 := goldbachB10LogDensity_nonneg (goldbachB10LogGridCell_subset_ambientBox hn hq hxq)
  nlinarith [mul_le_mul_of_nonneg_right hk hd0]

private lemma goldbachB10LogGrid_upperKernel_sub_le {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (_hq : q ∈ goldbachB10LogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogGridCell n q) :
    0 ≤ 1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1)) - goldbachB10LogKernel x ∧
    1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
      goldbachB10BetaGridPoint n (q.2 + 1)) - goldbachB10LogKernel x ≤ 6 / (n : ℝ) := by
  change
    x.1 ∈ Ioc (goldbachB10AlphaGridPoint n q.1) (goldbachB10AlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB10BetaGridPoint n q.2) (goldbachB10BetaGridPoint n (q.2 + 1))
    at hx
  rw [goldbachB10AlphaGridPoint_succ hn, goldbachB10BetaGridPoint_succ hn] at hx
  have hstep :
      goldbachB10AlphaGridStep n + goldbachB10BetaGridStep n =
        (239 / 660 : ℝ) / n := by
    unfold goldbachB10AlphaGridStep goldbachB10BetaGridStep
      goldbachB10AlphaGridWidth goldbachB10BetaGridWidth
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
    ring
  have hden : (1 / 4 : ℝ) ≤
      1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
        (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) := by
    have hα := goldbachB10AlphaGridPoint_succ_le_end hn q.1.isLt
    have hβ := goldbachB10BetaGridPoint_succ_le_end hn q.2.isLt
    have hsum :
        goldbachB10AlphaGridPoint n (q.1 + 1) +
          goldbachB10BetaGridPoint n (q.2 + 1) ≤
        goldbachB10Gamma + goldbachB10BetaGridEnd := by
      exact add_le_add hα hβ
    dsimp [goldbachB10Gamma, goldbachB10BetaGridEnd] at hsum ⊢
    have hsucc :
        goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n +
            (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) =
          goldbachB10AlphaGridPoint n (q.1 + 1) +
            goldbachB10BetaGridPoint n (q.2 + 1) := by
      calc
        goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n +
            (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n)
            = (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) +
                (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) := by ring
        _ = goldbachB10AlphaGridPoint n (q.1 + 1) +
              goldbachB10BetaGridPoint n (q.2 + 1) := by
                rw [goldbachB10AlphaGridPoint_succ hn, goldbachB10BetaGridPoint_succ hn]
    calc
      (1 / 4 : ℝ) ≤ 1 - (goldbachB10AlphaGridPoint n (q.1 + 1) +
        goldbachB10BetaGridPoint n (q.2 + 1)) := by
          have hsum' :
              goldbachB10AlphaGridPoint n (q.1 + 1) +
                goldbachB10BetaGridPoint n (q.2 + 1) ≤ (47 / 66 : ℝ) := by
            norm_num at hsum ⊢
            linarith
          linarith
      _ = 1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
          (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) := by
            rw [← hsucc]
            ring
  have hdenx : (1 / 4 : ℝ) ≤ 1 - x.1 - x.2 := by
    linarith [hx.1.2, hx.2.2, hden]
  have hdelta :
      0 ≤
        (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) +
          (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) - x.1 - x.2 ∧
      (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) +
          (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) - x.1 - x.2 ≤
        (239 / 660 : ℝ) / n := by
    constructor
    · linarith [hx.1.2, hx.2.2]
    · calc
        (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) +
            (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) - x.1 - x.2
            ≤ goldbachB10AlphaGridStep n + goldbachB10BetaGridStep n := by
              linarith [hx.1.1, hx.2.1]
        _ = (239 / 660 : ℝ) / n := hstep
  have hprod : (1 / 16 : ℝ) ≤
      (1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
        (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n)) * (1 - x.1 - x.2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hden) (sub_nonneg.mpr hdenx)]
  have hformula :
      1 / (1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
        (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n)) - goldbachB10LogKernel x =
      ((goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) +
        (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) - x.1 - x.2) /
      ((1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
        (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n)) * (1 - x.1 - x.2)) := by
    unfold goldbachB10LogKernel liuLogKernel
    field_simp
    ring
  rw [goldbachB10AlphaGridPoint_succ hn, goldbachB10BetaGridPoint_succ hn, hformula]
  constructor
  · exact div_nonneg hdelta.1 (by positivity)
  · have hInv :
        1 /
          ((1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
            (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n)) *
            (1 - x.1 - x.2)) ≤ 16 := by
      simpa using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hprod)
    have hmul :
        ((goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) +
            (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) - x.1 - x.2) /
            ((1 - (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) -
              (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n)) * (1 - x.1 - x.2)) ≤
          ((239 / 660 : ℝ) / n) * 16 := by
      rw [div_eq_mul_inv]
      simpa [one_div] using mul_le_mul hdelta.2 hInv (by positivity) (by positivity)
    have herr : ((239 / 660 : ℝ) / n) * 16 ≤ 6 / (n : ℝ) := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [hnreal.ne']
      norm_num
    exact hmul.trans herr

private lemma goldbachB10LogGridUpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB10LogSourceRegion) :
    goldbachB10LogGridUpperIntegrand n x ≤ goldbachB10LogIntegrand x + 240 / (n : ℝ) := by
  have hxregion := goldbachB10LogSourceRegion_subset_gridRegion hn hx
  rw [goldbachB10LogGridRegion] at hxregion
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hxregion
  rw [goldbachB10LogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hbox := goldbachB10LogGridCell_subset_ambientBox hn hq hxq
  have hd0 := goldbachB10LogDensity_nonneg hbox
  have hd := goldbachB10LogDensity_le_forty hbox
  have hk := goldbachB10LogGrid_upperKernel_sub_le hn hq hxq
  have hmul :
      (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
          goldbachB10BetaGridPoint n (q.2 + 1)) - goldbachB10LogKernel x) *
          goldbachB10LogDensity x ≤ (6 / (n : ℝ)) * 40 :=
    mul_le_mul (by
      have hk' := hk.2
      exact hk') hd hd0 (by positivity)
  have hconst : (6 / (n : ℝ)) * 40 = 240 / (n : ℝ) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp [hnreal.ne']
    ring
  unfold goldbachB10LogIntegrand liuLogIntegrand
  calc
    _ = goldbachB10LogKernel x * goldbachB10LogDensity x +
        (1 / (1 - goldbachB10AlphaGridPoint n (q.1 + 1) -
          goldbachB10BetaGridPoint n (q.2 + 1)) - goldbachB10LogKernel x) *
            goldbachB10LogDensity x := by ring
    _ ≤ goldbachB10LogKernel x * goldbachB10LogDensity x + 240 / (n : ℝ) := by
      rw [← hconst]
      linarith

private lemma measurableSet_goldbachB10LeftStrip (n : ℕ) :
    MeasurableSet (goldbachB10LeftStrip n) :=
  measurableSet_Ioc.prod measurableSet_Icc

private lemma measurableSet_goldbachB10BottomStrip (n : ℕ) :
    MeasurableSet (goldbachB10BottomStrip n) :=
  measurableSet_Icc.prod measurableSet_Ioc

private lemma measurableSet_goldbachB10ObliqueStrip (n : ℕ) :
    MeasurableSet (goldbachB10ObliqueStrip n) := by
  change MeasurableSet
    (Prod.fst ⁻¹' Icc goldbachB10Beta goldbachB10Gamma ∩
      ({x : ℝ × ℝ | (1 - x.1) / 2 < x.2} ∩
        {x : ℝ × ℝ |
          x.2 < (1 - x.1) / 2 +
            (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2}))
  exact (measurable_fst measurableSet_Icc).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

private lemma volume_goldbachB10LeftStrip (n : ℕ) (hn : 0 < n) :
    volume (goldbachB10LeftStrip n) =
      ENNReal.ofReal ((95 / 2904 : ℝ) / n) := by
  unfold goldbachB10LeftStrip
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod]
  have hstep :
      goldbachB10AlphaGridStep n = (19 / 110 : ℝ) / n := by
    unfold goldbachB10AlphaGridStep goldbachB10AlphaGridWidth
    ring
  have hlen :
      goldbachB10Beta - (goldbachB10Beta - (19 / 110 : ℝ) / n) =
        (19 / 110 : ℝ) / n := by ring
  have hheight : goldbachB10BetaGridEnd - goldbachB10BetaGridStart = (25 / 132 : ℝ) := by
    dsimp [goldbachB10BetaGridEnd, goldbachB10BetaGridStart]
    ring
  rw [Real.volume_Ioc, Real.volume_Icc, hstep, hlen, hheight]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (19 / 110 : ℝ) / n)]
  congr 1
  field_simp [hnreal.ne']
  ring

private lemma volume_goldbachB10BottomStrip (n : ℕ) (hn : 0 < n) :
    volume (goldbachB10BottomStrip n) =
      ENNReal.ofReal ((125 / 4356 : ℝ) / n) := by
  unfold goldbachB10BottomStrip
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod]
  have hstep :
      goldbachB10BetaGridStep n = (25 / 132 : ℝ) / n := by
    unfold goldbachB10BetaGridStep goldbachB10BetaGridWidth
    ring
  have hwidth : goldbachB10Gamma - goldbachB10Beta = (5 / 33 : ℝ) := by
    dsimp [goldbachB10Gamma, goldbachB10Beta]
    ring
  have hlen :
      goldbachB10Gamma - (goldbachB10Gamma - (25 / 132 : ℝ) / n) =
        (25 / 132 : ℝ) / n := by ring
  rw [Real.volume_Icc, Real.volume_Ioc, hwidth, hstep, hlen]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (5 / 33 : ℝ))]
  congr 1
  field_simp [hnreal.ne']
  ring

private lemma volume_goldbachB10ObliqueStrip (n : ℕ) (hn : 0 < n) :
    volume (goldbachB10ObliqueStrip n) =
      ENNReal.ofReal ((91 / 2178 : ℝ) / n) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.prod_apply (measurableSet_goldbachB10ObliqueStrip n)]
  have hsection (u : ℝ) :
      Prod.mk u ⁻¹' goldbachB10ObliqueStrip n =
        if u ∈ Icc goldbachB10Beta goldbachB10Gamma then
          Ioo ((1 - u) / 2)
            ((1 - u) / 2 +
              (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2)
        else ∅ := by
    ext v
    simp [goldbachB10ObliqueStrip, and_assoc]
  have hfun :
      (fun u : ℝ => volume (Prod.mk u ⁻¹' goldbachB10ObliqueStrip n)) =
        (Icc goldbachB10Beta goldbachB10Gamma).indicator
          (fun u => volume
            (Ioo ((1 - u) / 2)
              ((1 - u) / 2 +
                (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2))) := by
    funext u
    rw [hsection]
    by_cases hu : u ∈ Icc goldbachB10Beta goldbachB10Gamma
    · rw [if_pos hu, Set.indicator_of_mem hu, Real.volume_Ioo]
    · rw [if_neg hu, Set.indicator_of_notMem hu, measure_empty]
  rw [hfun, MeasureTheory.lintegral_indicator measurableSet_Icc]
  simp_rw [Real.volume_Ioo]
  have hdiff (u : ℝ) :
      (1 - u) / 2 + (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2 -
        (1 - u) / 2 =
      (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2 := by ring
  simp_rw [hdiff]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
  have hbasewidth : goldbachB10Gamma - goldbachB10Beta = (5 / 33 : ℝ) := by
    dsimp [goldbachB10Gamma, goldbachB10Beta]
    ring
  have hwidth :
      (goldbachB10AlphaGridStep n + 2 * goldbachB10BetaGridStep n) / 2 =
        (91 / 330 : ℝ) / n := by
    unfold goldbachB10AlphaGridStep goldbachB10BetaGridStep
      goldbachB10AlphaGridWidth goldbachB10BetaGridWidth
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
    ring
  rw [hbasewidth, hwidth, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (91 / 330 : ℝ) / n)]
  congr 1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [hnreal.ne']
  ring

private lemma goldbachB10LogGridRegion_excess_subset {n : ℕ} (hn : 0 < n) :
    goldbachB10LogGridRegion n \ goldbachB10LogSourceRegion ⊆
      (goldbachB10LeftStrip n ∪ goldbachB10BottomStrip n) ∪ goldbachB10ObliqueStrip n := by
  rintro x ⟨hg, hs⟩
  rw [goldbachB10LogGridRegion] at hg
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hg
  have hxq' :
      x.1 ∈ Ioc (goldbachB10AlphaGridPoint n q.1)
          (goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n) ∧
        x.2 ∈ Ioc (goldbachB10BetaGridPoint n q.2)
          (goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n) := by
    simpa [goldbachB10LogGridCell, goldbachB10AlphaGridPoint_succ hn,
      goldbachB10BetaGridPoint_succ hn] using hxq
  have hqSel := (show
      goldbachB10Beta ≤ goldbachB10AlphaGridPoint n (q.1 + 1) ∧
        goldbachB10Gamma ≤ goldbachB10BetaGridPoint n (q.2 + 1) ∧
        goldbachB10AlphaGridPoint n q.1 + 2 * goldbachB10BetaGridPoint n q.2 < 1 from by
      rw [goldbachB10LogGridCells, Finset.mem_filter] at hq
      exact hq.2)
  have hgeom := goldbachB10LogGridRegion_geometry hn hg
  by_cases hleft : x.1 ≤ goldbachB10Beta
  · have hxleft : x ∈ goldbachB10LeftStrip n := by
      refine ⟨?_, ?_⟩
      · have hright : goldbachB10Beta ≤
            goldbachB10AlphaGridPoint n q.1 + goldbachB10AlphaGridStep n := by
          simpa [goldbachB10AlphaGridPoint_succ hn] using hqSel.1
        exact ⟨by linarith [hxq.1.1, hright], hleft⟩
      · exact ⟨hgeom.2.1.1.le, hgeom.2.1.2⟩
    exact Or.inl (Or.inl hxleft)
  · have hβ : goldbachB10Beta < x.1 := lt_of_not_ge hleft
    by_cases hbottom : x.2 ≤ goldbachB10Gamma
    · have hxbottom : x ∈ goldbachB10BottomStrip n := by
        refine ⟨⟨hβ.le, hgeom.1.2⟩, ?_⟩
        have htop : goldbachB10Gamma ≤
            goldbachB10BetaGridPoint n q.2 + goldbachB10BetaGridStep n := by
          simpa [goldbachB10BetaGridPoint_succ hn] using hqSel.2.1
        exact ⟨by linarith [hxq'.2.1, htop], hbottom⟩
      exact Or.inl (Or.inr hxbottom)
    · have hγ : goldbachB10Gamma < x.2 := lt_of_not_ge hbottom
      have habove : (1 - x.1) / 2 < x.2 := by
        by_contra h
        apply hs
        exact ⟨⟨hβ, hgeom.1.2⟩, ⟨hγ, le_of_not_gt h⟩⟩
      have hxoblique : x ∈ goldbachB10ObliqueStrip n := by
        refine ⟨⟨hβ.le, hgeom.1.2⟩, habove, ?_⟩
        linarith
      exact Or.inr hxoblique

/-- The selected B10 upper sum exceeds the exact integral by at most `260/n`. -/
theorem goldbachB10LogGridUpperSum_sub_mainIntegral_le
    (n : ℕ) (hn : 0 < n) :
    goldbachB10LogGridUpperSum n - goldbachB10MainIntegral ≤ 260 / (n : ℝ) := by
  classical
  let E : Fin 3 → Set (ℝ × ℝ) :=
    ![goldbachB10LeftStrip n, goldbachB10BottomStrip n, goldbachB10ObliqueStrip n]
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    fin_cases i
    · exact measurableSet_goldbachB10LeftStrip n
    · exact measurableSet_goldbachB10BottomStrip n
    · exact measurableSet_goldbachB10ObliqueStrip n
  have hEf : ∀ i, volume (E i) ≠ ∞ := by
    intro i
    fin_cases i <;> simp [E, volume_goldbachB10LeftStrip n hn,
      volume_goldbachB10BottomStrip n hn, volume_goldbachB10ObliqueStrip n hn]
  have h := MathlibNt.Analysis.IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover
    volume (goldbachB10LogGridRegion n) goldbachB10LogSourceRegion
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) E
    (goldbachB10LogGridUpperIntegrand n) goldbachB10LogIntegrand (240 / (n : ℝ)) 160
    (integrable_goldbachB10LogGridUpperIntegrand n hn)
    (integrableOn_goldbachB10LogIntegrand measurableSet_goldbachB10LogSourceRegion
      goldbachB10LogSourceRegion_subset_ambientBox)
    measurableSet_goldbachB10LogSourceRegion (measurableSet_Icc.prod measurableSet_Icc)
    (by rw [volume_unitBox]; norm_num) hEm hEf (by positivity) (by norm_num)
    (fun _ hx => goldbachB10LogIntegrand_nonneg
      (goldbachB10LogSourceRegion_subset_ambientBox hx))
    (fun _ hx => goldbachB10LogGridUpperIntegrand_eq_zero_of_notMem hx)
    (by
      intro x hx
      have hb := goldbachB10LogSourceRegion_subset_ambientBox hx.2
      dsimp [goldbachB10LogAmbientBox, goldbachB10AlphaGridStart,
        goldbachB10Gamma, goldbachB10BetaGridStart, goldbachB10BetaGridEnd] at hb
      exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩)
    (fun _ hx => goldbachB10LogGridUpperIntegrand_le_integrand_add hn hx.2)
    (by
      intro x hx
      rcases goldbachB10LogGridRegion_excess_subset hn hx with (hl | hb) | ho
      · exact ⟨0, hl⟩
      · exact ⟨1, hb⟩
      · exact ⟨2, ho⟩)
    (fun _ hx => goldbachB10LogGridUpperIntegrand_le_oneSixty hn hx.1)
  rw [← goldbachB10LogGridUpperSum_eq_integral n hn,
    ← goldbachB10MainIntegral_eq_setIntegral, Fin.sum_univ_three] at h
  dsimp [E] at h
  simp only [Measure.real_def, volume_unitBox, volume_goldbachB10LeftStrip n hn,
    volume_goldbachB10BottomStrip n hn, volume_goldbachB10ObliqueStrip n hn,
    ENNReal.toReal_one, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (95 / 2904 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (125 / 4356 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (91 / 2178 : ℝ) / n)] at h
  refine h.trans ?_
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [hnreal.ne']
  norm_num

/-- The B10 logarithmic-grid upper sums converge to the exact printed integral
`I10` as the mesh tends to zero. -/
theorem tendsto_goldbachB10LogGridUpperSum_mainIntegral :
    Tendsto (fun n : ℕ => goldbachB10LogGridUpperSum (n + 1)) atTop
      (nhds goldbachB10MainIntegral) := by
  have herror :
      Tendsto (fun n : ℕ => (260 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, mul_zero] using
      (Tendsto.const_mul (260 : ℝ)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)))
  have hdiff :
      Tendsto
        (fun n : ℕ => goldbachB10LogGridUpperSum (n + 1) - goldbachB10MainIntegral)
        atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n =>
        sub_nonneg.mpr
          (goldbachB10MainIntegral_le_goldbachB10LogGridUpperSum (n + 1) (Nat.succ_pos n))
    · exact Filter.Eventually.of_forall fun n =>
        goldbachB10LogGridUpperSum_sub_mainIntegral_le (n + 1) (Nat.succ_pos n)
    · exact herror
  have hconst :
      Tendsto (fun _ : ℕ => goldbachB10MainIntegral) atTop
        (nhds goldbachB10MainIntegral) :=
    tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hdiff.add hconst

/-- Eventual epsilon form of `goldbachB10LogGridUpperSum → I10`. -/
theorem eventually_abs_goldbachB10LogGridUpperSum_sub_mainIntegral_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      |goldbachB10LogGridUpperSum (n + 1) - goldbachB10MainIntegral| < ε := by
  have h := tendsto_goldbachB10LogGridUpperSum_mainIntegral
  rw [Metric.tendsto_nhds] at h
  filter_upwards [h ε hε] with n hn
  simpa only [Real.dist_eq] using hn

/-- Threshold form of `goldbachB10LogGridUpperSum → I10`. -/
theorem exists_abs_goldbachB10LogGridUpperSum_sub_mainIntegral_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |goldbachB10LogGridUpperSum (n + 1) - goldbachB10MainIntegral| < ε := by
  simpa only [eventually_atTop] using
    eventually_abs_goldbachB10LogGridUpperSum_sub_mainIntegral_lt hε

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig