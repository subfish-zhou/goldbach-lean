import MathlibNt.Wu2008DoubleSieve.ImprovementMonotonicity
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthCarriers

/-!
# Fixed-delta geometry for the actual truncated sixth lower bound

The classical coefficient is the existing normalized canonical lower
coefficient, not its initial logarithmic formula. The improvement is
the actual fixed-delta limit and is restricted to the admissible side.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical

noncomputable def truncatedSixthLowerAlpha : ℝ := 100 / 1327
noncomputable def truncatedSixthLowerBeta : ℝ := 25 / 206
noncomputable def truncatedSixthLowerSigma : ℝ := 1 / 2 - 3 * truncatedSixthLowerAlpha
noncomputable def truncatedSixthLowerLambda : ℝ := 1 / 2 - 2 * truncatedSixthLowerAlpha
noncomputable def truncatedSixthLowerC (δ : ℝ) : ℝ := 1 / 2 - δ
noncomputable def truncatedSixthLowerS (δ x y : ℝ) : ℝ :=
  (truncatedSixthLowerC δ - x - y) / truncatedSixthLowerAlpha

def truncatedSixthLowerRegion (δ x y : ℝ) : Prop :=
  truncatedSixthLowerAlpha ≤ x ∧ x ≤ truncatedSixthLowerBeta ∧
    truncatedSixthLowerBeta ≤ y ∧ y ≤ truncatedSixthLowerSigma ∧
    x + y ≤ truncatedSixthLowerC δ - 2 * truncatedSixthLowerAlpha

def truncatedSixthLowerAdmissibleRegion (δ x y : ℝ) : Prop :=
  truncatedSixthLowerRegion δ x y ∧ y ≤ truncatedSixthLowerC δ / 2

def truncatedSixthLowerWedge (δ x y : ℝ) : Prop :=
  truncatedSixthLowerRegion δ x y ∧ truncatedSixthLowerC δ / 2 < y

noncomputable def truncatedSixthLowerFdelta (δ : ℝ) : ℝ :=
  4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
    ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
      if truncatedSixthLowerRegion δ x y then
        wuLowerCoefficient (truncatedSixthLowerS δ x y) /
          (x * y * (truncatedSixthLowerC δ - x - y)) else 0

noncomputable def truncatedSixthLowerHadmdelta (δ : ℝ) : ℝ :=
  4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
    ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
      if truncatedSixthLowerAdmissibleRegion δ x y then
        wuImprovementLimit false δ (truncatedSixthLowerS δ x y) /
          (x * y * (truncatedSixthLowerC δ - x - y)) else 0

noncomputable def truncatedSixthLowerF6lin : ℝ := truncatedSixthLowerFdelta 0

theorem truncatedSixthLower_parameters :
    0 < truncatedSixthLowerAlpha ∧
      truncatedSixthLowerAlpha < truncatedSixthLowerBeta ∧
      truncatedSixthLowerBeta < truncatedSixthLowerSigma ∧
      truncatedSixthLowerSigma < 1 / 3 ∧
      0 < 2 * truncatedSixthLowerAlpha - truncatedSixthLowerBeta := by
  norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerBeta, truncatedSixthLowerSigma]

theorem truncatedSixthLower_region_bounds {δ x y : ℝ}
    (hδ : 0 ≤ δ) (h : truncatedSixthLowerRegion δ x y) :
    0 < x ∧ 0 < y ∧
      2 * truncatedSixthLowerAlpha ≤ truncatedSixthLowerC δ - x - y ∧
      2 ≤ truncatedSixthLowerS δ x y ∧ truncatedSixthLowerS δ x y ≤ 5 := by
  obtain ⟨hx, _, hy, _, hsum⟩ := h
  have hp := truncatedSixthLower_parameters
  have hd : 2 * truncatedSixthLowerAlpha ≤ truncatedSixthLowerC δ - x - y := by linarith
  refine ⟨hp.1.trans_le hx, (hp.1.trans hp.2.1).trans_le hy, hd, ?_, ?_⟩
  · exact (le_div_iff₀ hp.1).mpr hd
  · apply (div_le_iff₀ hp.1).mpr
    norm_num [truncatedSixthLowerC, truncatedSixthLowerAlpha, truncatedSixthLowerBeta] at *
    linarith

theorem truncatedSixthLower_prefix_slack {δ x y : ℝ}
    (h : truncatedSixthLowerRegion δ x y) :
    2 * x + y ≤ truncatedSixthLowerC δ -
      (2 * truncatedSixthLowerAlpha - truncatedSixthLowerBeta) := by
  obtain ⟨_, hx, _, _, hsum⟩ := h
  linarith

theorem truncatedSixthLower_retained {δ x y : ℝ}
    (hδ : 0 < δ) (h : truncatedSixthLowerRegion δ x y) :
    x + y < truncatedSixthLowerLambda := by
  have hs := h.2.2.2.2
  unfold truncatedSixthLowerC at hs
  unfold truncatedSixthLowerLambda
  linarith

theorem truncatedSixthLower_regions_disjoint (δ x y : ℝ) :
    ¬(truncatedSixthLowerAdmissibleRegion δ x y ∧ truncatedSixthLowerWedge δ x y) :=
  fun h => (not_lt_of_ge h.1.2) h.2.2

theorem truncatedSixthLower_regions_cover (δ x y : ℝ) :
    truncatedSixthLowerRegion δ x y ↔
      truncatedSixthLowerAdmissibleRegion δ x y ∨ truncatedSixthLowerWedge δ x y := by
  unfold truncatedSixthLowerAdmissibleRegion truncatedSixthLowerWedge
  exact ⟨fun h => (le_or_gt y (truncatedSixthLowerC δ / 2)).elim
    (fun hy => Or.inl ⟨h, hy⟩) (fun hy => Or.inr ⟨h, hy⟩),
    fun h => h.elim And.left And.left⟩

theorem truncatedSixthLower_depth_two {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    δ ^ 3 < truncatedSixthLowerAlpha := by
  have hpow := pow_le_pow_left₀ hδ.le hδhi.le 3
  norm_num [truncatedSixthLowerAlpha] at *
  linarith

end Wu2008DoubleSieve
