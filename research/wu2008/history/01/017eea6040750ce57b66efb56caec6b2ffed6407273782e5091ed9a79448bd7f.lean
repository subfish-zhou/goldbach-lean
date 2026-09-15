import MathlibNt.Wu2008DoubleSieve.TableGainComposition
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthZeroDeltaEndpoint

/-!
# Continuity of the explicit nine-coordinate coefficients

Only the finite logarithmic coefficient map is varied. No continuity
of either actual improvement function in delta is used.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Classical Topology BigOperators

theorem truncatedSixthTable_B_continuous (j : Fin 9) :
    Continuous (fun s => tableGainB s j) := by
  have hc (n : ℕ) : Continuous (fun s => tableGainClip s n) := by
    unfold tableGainClip
    fun_prop
  have hw (i : Fin 29) : Continuous (fun s => tableGainWeight s i) :=
    ((hc (i.val + 1)).div (hc i.val) (fun s => (tableGainClip_pos s i.val).ne')).log
      (fun s => (div_pos (tableGainClip_pos s (i.val + 1))
        (tableGainClip_pos s i.val)).ne')
  exact continuous_finsetSum _ (fun i _ => (hw i).mul_const (tableGainE i j))

theorem truncatedSixthTable_B_bound (j : Fin 9) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (2 : ℝ) 5, tableGainB s j ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (truncatedSixthTable_B_continuous j).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs
  exact (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC s hs)).trans
    (le_max_left _ _)

noncomputable def truncatedSixthTableRegular (δ : ℝ) (j : Fin 9) (v : ℝ × ℝ) : ℝ :=
  tableGainB (truncatedSixthMassClip (truncatedSixthLowerS δ v.1 v.2)) j /
    truncatedSixthMassDenominator δ v

theorem truncatedSixthTable_regular_continuous (j : Fin 9) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => truncatedSixthTableRegular p.1 j p.2) := by
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      truncatedSixthMassClip (truncatedSixthLowerS p.1 p.2.1 p.2.2)) := by
    unfold truncatedSixthMassClip truncatedSixthLowerS truncatedSixthLowerC
    fun_prop
  have hd : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      truncatedSixthMassDenominator p.1 p.2) := by
    unfold truncatedSixthMassDenominator truncatedSixthLowerC
    fun_prop
  exact ((truncatedSixthTable_B_continuous j).comp hs).div hd
    (fun p => (truncatedSixthMass_denominator_pos p.1 p.2).ne')

theorem truncatedSixthTable_regular_eq {δ : ℝ} (hδ : 0 ≤ δ)
    (j : Fin 9) {v : ℝ × ℝ} (hv : truncatedSixthLowerRegion δ v.1 v.2) :
    truncatedSixthTableRegular δ j v =
      tableGainB (truncatedSixthLowerS δ v.1 v.2) j /
        (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) := by
  rw [truncatedSixthTableRegular,
    truncatedSixthMass_clip_eq (truncatedSixthLower_region_bounds hδ hv).2.2.2,
    truncatedSixthMass_denominator_eq hδ hv]

theorem truncatedSixthTable_regular_nonneg (δ : ℝ) (j : Fin 9) (v : ℝ × ℝ) :
    0 ≤ truncatedSixthTableRegular δ j v :=
  div_nonneg (tableGainB_nonneg _ _) (truncatedSixthMass_denominator_pos δ v).le

theorem truncatedSixthTable_regular_bound (j : Fin 9) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ v, truncatedSixthTableRegular δ j v ≤ C := by
  obtain ⟨M, hM, hb⟩ := truncatedSixthTable_B_bound j
  let D := truncatedSixthLowerAlpha * truncatedSixthLowerBeta *
    (2 * truncatedSixthLowerAlpha)
  have hα := truncatedSixthLower_parameters.1
  have hβ := hα.trans truncatedSixthLower_parameters.2.1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨M / D, div_nonneg hM hD.le, ?_⟩
  intro δ v
  have hd : D ≤ truncatedSixthMassDenominator δ v := by
    apply mul_le_mul
      (mul_le_mul (le_max_left _ _) (le_max_left _ _) hβ.le
        (hα.le.trans (le_max_left _ _)))
      (le_max_left _ _) (by positivity) (by positivity)
  exact div_le_div₀ hM (hb _ (truncatedSixthMass_clip_bounds _)) hD hd

end Wu2008DoubleSieve
