import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A closed horizontal window and a half-open strip below its diagonal. -/
def goldbachAffineDiagonalStrip (a b h : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ p.2 ∈ Ioc (p.1 - h) p.1}

theorem measurableSet_goldbachAffineDiagonalStrip (a b h : ℝ) :
    MeasurableSet (goldbachAffineDiagonalStrip a b h) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((isOpen_lt (continuous_fst.sub continuous_const) continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd continuous_fst).measurableSet)

theorem goldbachAffineDiagonalStrip_section (a b h u : ℝ) :
    Prod.mk u ⁻¹' goldbachAffineDiagonalStrip a b h =
      if u ∈ Icc a b then Ioc (u - h) u else ∅ := by
  classical
  ext v
  simp [goldbachAffineDiagonalStrip]

/-- Exact volume from vertical sections, not a bound on finite prime points. -/
theorem volume_goldbachAffineDiagonalStrip (a b h : ℝ) (hh : 0 ≤ h) :
    volume (goldbachAffineDiagonalStrip a b h) = ENNReal.ofReal (h * (b - a)) := by
  classical
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.prod_apply (measurableSet_goldbachAffineDiagonalStrip a b h)]
  have hfun : (fun u : ℝ => volume (Prod.mk u ⁻¹' goldbachAffineDiagonalStrip a b h)) =
      (Icc a b).indicator (fun _ : ℝ => ENNReal.ofReal h) := by
    funext u
    rw [goldbachAffineDiagonalStrip_section]
    by_cases hu : u ∈ Icc a b
    · rw [if_pos hu, indicator_of_mem hu, Real.volume_Ioc]
      congr 1
      ring
    · rw [if_neg hu, indicator_of_notMem hu, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Icc, setLIntegral_const,
    Real.volume_Icc, ← ENNReal.ofReal_mul hh]

/-- The diagonal excess strip for the B8 ambient mesh widths 1/12 and 5/44.
This definition does not assert the still separate grid-excess classification. -/
def goldbachB8DiagonalStrip (n : ℕ) : Set (ℝ × ℝ) :=
  goldbachAffineDiagonalStrip (3 / 11) (1 / 3)
    ((1 / 12 : ℝ) / n + (5 / 44 : ℝ) / n)

theorem measurableSet_goldbachB8DiagonalStrip (n : ℕ) :
    MeasurableSet (goldbachB8DiagonalStrip n) :=
  measurableSet_goldbachAffineDiagonalStrip _ _ _

theorem volume_goldbachB8DiagonalStrip (n : ℕ) :
    volume (goldbachB8DiagonalStrip n) = ENNReal.ofReal ((13 / 1089 : ℝ) / n) := by
  rw [goldbachB8DiagonalStrip, volume_goldbachAffineDiagonalStrip _ _ _ (by positivity)]
  congr 1
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig