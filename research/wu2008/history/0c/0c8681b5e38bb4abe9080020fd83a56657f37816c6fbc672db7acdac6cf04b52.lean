import SrcNineAnalyticIntegralSplit

noncomputable section
namespace WuSource.SrcNine.Analytic
open Set MeasureTheory Wu2008DoubleSieve
open scoped BigOperators Interval

theorem buchstab_below_one {u : ℝ} (hu : u ≤ 1) :
    LiLiuPrereqBuchstab.buchstab u = 1 := by
  rw [LiLiuPrereqBuchstab.buchstab_eq_approx 0 u (by norm_num; linarith),
    LiLiuPrereqBuchstab.approx.eq_1, max_eq_left hu]
  norm_num

theorem buchstab_global_bounds (u : ℝ) :
    0 ≤ LiLiuPrereqBuchstab.buchstab u ∧ LiLiuPrereqBuchstab.buchstab u ≤ 1 := by
  by_cases hu : 1 ≤ u
  · exact ⟨LiLiuPrereqBuchstab.buchstab_nonneg hu, LiLiuPrereqBuchstab.buchstab_le_one hu⟩
  · rw [buchstab_below_one (le_of_lt (lt_of_not_ge hu))]
    norm_num

theorem rawWeight_bounds {n : ℕ} (j : Fin n) (phi : ℝ) {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) :
    0 ≤ rawWeight j phi t ∧ rawWeight j phi t ≤ 10 * continuousDensity t := by
  have htj := (ht j (mem_univ j)).1
  have hj : 0 < t j := by linarith
  have hw := buchstab_global_bounds ((phi - ∑ i, t i) / t j)
  have hq : LiLiuPrereqBuchstab.buchstab ((phi - ∑ i, t i) / t j) / t j ≤ 10 := by
    apply (div_le_iff₀ hj).mpr
    linarith [hw.2]
  exact ⟨mul_nonneg (div_nonneg hw.1 hj.le) (continuousDensity_nonneg ht),
    mul_le_mul_of_nonneg_right hq (continuousDensity_nonneg ht)⟩

theorem rawIntegral_bounds {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hm : MeasurableSet D) (hD : D ⊆ continuousCube n) :
    0 ≤ rawIntegral j D phi ∧
      rawIntegral j D phi ≤ 10 * ∫ t in D, continuousDensity t := by
  have hd := (continuousDensity_integrable n).mono_set hD
  constructor
  · apply integral_nonneg_of_ae
    exact (ae_restrict_mem hm).mono (fun t ht => (rawWeight_bounds j phi (hD ht)).1)
  · rw [← integral_const_mul]
    apply integral_mono_ae (rawWeight_integrable j phi hD) (hd.const_mul 10)
    exact (ae_restrict_mem hm).mono (fun t ht => (rawWeight_bounds j phi (hD ht)).2)

theorem illegalIntegral_nonneg {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hm : MeasurableSet D) (hD : D ⊆ continuousCube n) :
    0 ≤ illegalIntegral j D phi :=
  (rawIntegral_bounds j phi (hm.diff (HighNonunitLegal.legal_measurable j phi))
    (sdiff_subset.trans hD)).1

theorem illegalIntegral_literal {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hm : MeasurableSet D) (hD : D ⊆ continuousCube n) :
    illegalIntegral j D phi =
      ∫ t in D \ HighNonunitLegal.legal j phi, 1 / (t j * ∏ i, t i) := by
  apply setIntegral_congr_fun (hm.diff (HighNonunitLegal.legal_measurable j phi))
  intro t ht
  have hj : 0 < t j := by
    have h := (hD ht.1 j (mem_univ j)).1
    linarith
  have hi : (phi - ∑ i, t i) / t j ≤ 1 := by
    apply (div_le_iff₀ hj).mpr
    have hnot := ht.2
    change ¬ (∑ i, t i) + t j ≤ phi at hnot
    linarith
  rw [rawWeight_literal, buchstab_below_one hi]

theorem raw_values_nonempty {n : ℕ} (j : Fin n) (D : Set (Fin n → ℝ)) :
    (rawIntegral j D '' Ici 2).Nonempty :=
  ⟨rawIntegral j D 2, 2, le_rfl, rfl⟩

theorem raw_values_bddAbove {n : ℕ} (j : Fin n) {D : Set (Fin n → ℝ)}
    (hm : MeasurableSet D) (hD : D ⊆ continuousCube n) :
    BddAbove (rawIntegral j D '' Ici 2) := by
  refine ⟨10 * ∫ t in D, continuousDensity t, ?_⟩
  rintro _ ⟨phi, _, rfl⟩
  exact (rawIntegral_bounds j phi hm hD).2

end WuSource.SrcNine.Analytic
