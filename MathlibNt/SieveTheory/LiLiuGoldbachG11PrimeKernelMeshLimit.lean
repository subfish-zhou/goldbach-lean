import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelMeshIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory Set
open scoped BigOperators Topology Interval

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11MeshUpperIntegrand (h : ℝ → ℝ) (n : ℕ)
    (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ∑ j ∈ goldbachG11MeshCells n,
    goldbachG11MeshCoeff h n j * (goldbachG11MeshCell n j).indicator goldbachG11MeshDensity x

def goldbachG11MeshUpperSum (h : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ goldbachG11MeshCells n, goldbachG11MeshCoeff h n j *
    goldbachG11LogBoxMass (goldbachG11MeshLo n j) (goldbachG11MeshHi n j)

theorem tendsto_goldbachG11MeshStep :
    Tendsto goldbachG11MeshStep atTop (nhds 0) := by
  unfold goldbachG11MeshStep
  simpa only [mul_one_div, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((4 / 33 : ℝ) - 4 / 53)

theorem tendsto_goldbachG11Mesh_sameCell (i : ∀ n : ℕ, Fin (n + 1))
    (y : ℕ → ℝ) {x : ℝ}
    (hx : ∀ n, x ∈ Icc (goldbachG11MeshPoint n (i n))
      (goldbachG11MeshPoint n ((i n).val + 1)))
    (hy : ∀ n, y n ∈ Icc (goldbachG11MeshPoint n (i n))
      (goldbachG11MeshPoint n ((i n).val + 1))) :
    Tendsto y atTop (nhds x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [tendsto_goldbachG11MeshStep.eventually (gt_mem_nhds hε)] with n hn
  have hxn := hx n
  have hyn := hy n
  rw [goldbachG11MeshPoint_succ] at hxn hyn
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hxn.2, hyn.1], by linarith [hyn.2, hxn.1]⟩

theorem tendsto_goldbachG11MeshSup (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (i : ∀ n : ℕ, Fin (n + 1)) {x : ℝ}
    (hx : ∀ n, x ∈ Icc (goldbachG11MeshPoint n (i n))
      (goldbachG11MeshPoint n ((i n).val + 1))) :
    Tendsto (fun n => goldbachG11MeshSup h n (i n)) atTop (nhds (h x)) := by
  choose y hy he using fun n => goldbachG11MeshSup_attained h hh n (i n)
  have ht := tendsto_goldbachG11Mesh_sameCell i y hx hy
  have ht' : Tendsto y atTop (nhdsWithin x (Icc (4 / 53 : ℝ) (4 / 33))) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall
      (fun n => goldbachG11MeshCell_subset n (i n) (hy n))⟩
  exact ((hh x (goldbachG11MeshCell_subset 0 (i 0) (hx 0))).tendsto.comp ht').congr he

theorem tendsto_goldbachG11MeshCoeff (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (j : ∀ n : ℕ, (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    {x : (ℝ × ℝ) × (ℝ × ℝ)} (hx : ∀ n, x ∈ goldbachG11MeshCell n (j n)) :
    Tendsto (fun n => goldbachG11MeshCoeff h n (j n)) atTop (nhds (h x.1.1 / x.1.2)) := by
  have hr := tendsto_goldbachG11MeshSup h hh (fun n => (j n).1.1)
    (fun n => ⟨(hx n).1.1.1.le, (hx n).1.1.2⟩)
  have hq := tendsto_goldbachG11Mesh_sameCell (fun n => (j n).1.2)
    (fun n => goldbachG11MeshPoint n (j n).1.2)
    (fun n => ⟨(hx n).1.2.1.le, (hx n).1.2.2⟩)
    (fun n => ⟨le_rfl, ((goldbachG11MeshPoint_strictMono n) (Nat.lt_succ_self _)).le⟩)
  have hqpos : 0 < x.1.2 :=
    (goldbachG11MeshPoint_pos 0 (j 0).1.2).trans (hx 0).1.2.1
  exact hr.div hq hqpos.ne'

theorem integrable_goldbachG11MeshUpperIntegrand (h : ℝ → ℝ) (n : ℕ) :
    Integrable (goldbachG11MeshUpperIntegrand h n) := by
  exact integrable_finsetSum _ fun j _ =>
    ((integrableOn_goldbachG11MeshDensity (measurableSet_goldbachG11MeshCell n j)
      (fun _ hx => goldbachG11MeshBox_subset_ambient
        (goldbachG11MeshCell_subset_box n j hx))).integrable_indicator
      (measurableSet_goldbachG11MeshCell n j)).const_mul _

theorem goldbachG11MeshUpperSum_eq_integral (h : ℝ → ℝ) (n : ℕ) :
    goldbachG11MeshUpperSum h n = ∫ x, goldbachG11MeshUpperIntegrand h n x := by
  unfold goldbachG11MeshUpperSum goldbachG11MeshUpperIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_indicator (measurableSet_goldbachG11MeshCell n j),
      goldbachG11LogBoxMass_eq_meshIntegral]
  · intro j _
    exact ((integrableOn_goldbachG11MeshDensity (measurableSet_goldbachG11MeshCell n j)
      (fun _ hx => goldbachG11MeshBox_subset_ambient
        (goldbachG11MeshCell_subset_box n j hx))).integrable_indicator
      (measurableSet_goldbachG11MeshCell n j)).const_mul _

theorem goldbachG11MeshUpperIntegrand_eq_of_mem (h : ℝ → ℝ) {n : ℕ}
    {j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))}
    (hj : j ∈ goldbachG11MeshCells n) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG11MeshCell n j) :
    goldbachG11MeshUpperIntegrand h n x = goldbachG11MeshCoeff h n j * goldbachG11MeshDensity x := by
  classical
  unfold goldbachG11MeshUpperIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro k _ hkj
    rw [indicator_of_notMem (fun hk => hkj (goldbachG11MeshCell_unique hk hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem goldbachG11MeshUpperIntegrand_eq_zero (h : ℝ → ℝ) {n : ℕ}
    {x : (ℝ × ℝ) × (ℝ × ℝ)} (hx : x ∉ goldbachG11MeshRegion n) :
    goldbachG11MeshUpperIntegrand h n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx (Set.mem_iUnion₂.mpr ⟨j, hj, h⟩)), mul_zero]

theorem goldbachG11MeshRegion_eventually_not_mem {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∉ goldbachG11MeshSource) :
    ∀ᶠ n : ℕ in atTop, x ∉ goldbachG11MeshRegion n := by
  by_cases hb : x ∈ goldbachG11MeshBox
  · have ho : ¬ (x.1.1 ≤ x.1.2 ∧ x.1.2 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2) :=
      fun ho => hx ⟨hb, ho⟩
    simp only [not_and_or, not_le] at ho
    rcases ho with hrq | hqs | hst
    · filter_upwards [tendsto_goldbachG11MeshStep.eventually
        (gt_mem_nhds (sub_pos.mpr hrq))] with n hn
      intro hmem
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
      have he := goldbachG11MeshCell_order_error hj hxj
      linarith [he.1]
    · filter_upwards [tendsto_goldbachG11MeshStep.eventually
        (gt_mem_nhds (sub_pos.mpr hqs))] with n hn
      intro hmem
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
      have he := goldbachG11MeshCell_order_error hj hxj
      linarith [he.2.1]
    · filter_upwards [tendsto_goldbachG11MeshStep.eventually
        (gt_mem_nhds (sub_pos.mpr hst))] with n hn
      intro hmem
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
      have he := goldbachG11MeshCell_order_error hj hxj
      linarith [he.2.2]
  · apply Eventually.of_forall
    intro n hmem
    obtain ⟨j, _, hxj⟩ := Set.mem_iUnion₂.mp hmem
    exact hb (goldbachG11MeshCell_subset_box n j hxj)

theorem tendsto_goldbachG11MeshUpperIntegrand (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    Tendsto (fun n => goldbachG11MeshUpperIntegrand h n x) atTop
      (nhds (goldbachG11MeshSource.indicator (goldbachG11MeshIntegrand h) x)) := by
  by_cases hx : x ∈ goldbachG11MeshSource
  · choose j hj hxj using fun n => goldbachG11MeshSource_cover n hx
    rw [indicator_of_mem hx]
    exact ((tendsto_goldbachG11MeshCoeff h hh j hxj).mul_const
      (goldbachG11MeshDensity x)).congr
        (fun n => (goldbachG11MeshUpperIntegrand_eq_of_mem h (hj n) (hxj n)).symm)
  · rw [indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [goldbachG11MeshRegion_eventually_not_mem hx] with n hn
    exact (goldbachG11MeshUpperIntegrand_eq_zero h hn).symm

theorem goldbachG11MeshCoeff_le (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), h x ≤ M)
    (n : ℕ) (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    goldbachG11MeshCoeff h n j ≤ M / (4 / 53) := by
  exact (div_le_div_of_nonneg_right (goldbachG11MeshSup_le h hh n j.1.1 hM)
    (goldbachG11MeshPoint_pos _ _).le).trans
      (div_le_div_of_nonneg_left hM0 (by norm_num)
        (goldbachG11MeshPoint_bounds n (by omega : (j.1.2 : ℕ) ≤ n + 1)).1)

theorem goldbachG11MeshUpperIntegrand_dominated (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), h x ≤ M)
    (n : ℕ) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖goldbachG11MeshUpperIntegrand h n x‖ ≤
      (M / (4 / 53)) * goldbachG11MeshAmbient.indicator goldbachG11MeshDensity x := by
  by_cases hx : x ∈ goldbachG11MeshRegion n
  · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    have hb := goldbachG11MeshBox_subset_ambient (goldbachG11MeshCell_subset_box n j hxj)
    have hd := goldbachG11MeshDensity_nonneg hb
    rw [goldbachG11MeshUpperIntegrand_eq_of_mem h hj hxj, indicator_of_mem hb,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (goldbachG11MeshCoeff_nonneg h hh hpos n j) hd)]
    exact mul_le_mul_of_nonneg_right (goldbachG11MeshCoeff_le h hh hM0 hM n j) hd
  · rw [goldbachG11MeshUpperIntegrand_eq_zero h hx, norm_zero]
    apply mul_nonneg (div_nonneg hM0 (by norm_num))
    by_cases hb : x ∈ goldbachG11MeshAmbient
    · rw [indicator_of_mem hb]
      exact goldbachG11MeshDensity_nonneg hb
    · rw [indicator_of_notMem hb]

theorem tendsto_goldbachG11MeshUpperSum (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x) :
    Tendsto (goldbachG11MeshUpperSum h) atTop (nhds (goldbachG11PrimeIntegral h)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hh
  have hb : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), h x ≤ max 0 M :=
    fun x hx => (hM (mem_image_of_mem h hx)).trans (le_max_right _ _)
  rw [goldbachG11PrimeIntegral_eq_meshSource h hh]
  change Tendsto (fun n => goldbachG11MeshUpperSum h n) atTop _
  simp only [goldbachG11MeshUpperSum_eq_integral]
  apply tendsto_integral_of_dominated_convergence
    (fun x => (max 0 M / (4 / 53)) *
      goldbachG11MeshAmbient.indicator goldbachG11MeshDensity x)
  · exact fun n => (integrable_goldbachG11MeshUpperIntegrand h n).aestronglyMeasurable
  · exact ((integrableOn_goldbachG11MeshDensity measurableSet_goldbachG11MeshAmbient
      Subset.rfl).integrable_indicator measurableSet_goldbachG11MeshAmbient).const_mul _
  · exact fun n => Eventually.of_forall
      (goldbachG11MeshUpperIntegrand_dominated h hh hpos (le_max_left _ _) hb n)
  · exact Eventually.of_forall (tendsto_goldbachG11MeshUpperIntegrand h hh)

theorem goldbachG11MeshUpperSum_exists_le_integral (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ n : ℕ, goldbachG11MeshUpperSum h n ≤ goldbachG11PrimeIntegral h + ν := by
  have he := (tendsto_goldbachG11MeshUpperSum h hh hpos).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ hν))
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, hn.le⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig