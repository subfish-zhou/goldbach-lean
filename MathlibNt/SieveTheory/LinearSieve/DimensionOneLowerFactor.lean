import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-! The explicit dimension-one lower-sieve factor and its continuity theorem.
Chen and Li-Liu specialize the same interval theorem at different points. -/

noncomputable section
namespace MathlibNt.SieveTheory.SwitchingPrinciple
open MeasureTheory intervalIntegral

/-- The inner Buchstab integral occurring in both terms of Chen's equations
(26)--(27). -/
noncomputable def jurkatRichertInnerIntegral (u : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..u - 1, Real.log (t - 1) / t

/-- The standard dimension-one lower linear-sieve factor on `4 ≤ s ≤ 6`.
It is the solution of `(s f(s))' = F(s - 1)` obtained from the preceding
upper-sieve branch. -/
noncomputable def dimensionOneLowerLinearSieveFactor (s : ℝ) : ℝ :=
  (2 * Real.exp Real.eulerMascheroniConstant / s) *
    (Real.log (s - 1) +
      ∫ u in (3 : ℝ)..s - 1, jurkatRichertInnerIntegral u / u)

lemma continuousOn_jurkatRichertInnerIntegral_three_five :
    ContinuousOn jurkatRichertInnerIntegral (Set.Icc (3 : ℝ) 5) := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hf : IntervalIntegrable f volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      linarith [ht.1]
  have hp : ContinuousOn (fun b => ∫ t in (2 : ℝ)..b, f t) (Set.Icc 2 4) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (2 : ℝ)) hf
      (by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] using h
  unfold jurkatRichertInnerIntegral
  change ContinuousOn (fun u => (∫ t in (2 : ℝ)..u - 1, f t)) (Set.Icc 3 5)
  apply hp.comp (continuousOn_id.sub continuousOn_const)
  intro u hu
  change 2 ≤ u - 1 ∧ u - 1 ≤ 4
  constructor <;> linarith [hu.1, hu.2]

/-- The explicit lower-sieve factor is continuous on the shared source interval. -/
theorem dimensionOneLowerLinearSieveFactor_continuousOn_four_six :
    ContinuousOn dimensionOneLowerLinearSieveFactor (Set.Icc (4 : ℝ) 6) := by
  have hinnerDiv : ContinuousOn
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) (Set.Icc (3 : ℝ) 5) := by
    apply ContinuousOn.div continuousOn_jurkatRichertInnerIntegral_three_five
      continuousOn_id
    intro u hu
    change u ≠ 0
    linarith [hu.1]
  have hinnerInt : IntervalIntegrable
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    exact hinnerDiv
  have hprimitive : ContinuousOn
      (fun b : ℝ => ∫ u in (3 : ℝ)..b, jurkatRichertInnerIntegral u / u)
      (Set.Icc (3 : ℝ) 5) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (3 : ℝ))
      hinnerInt
      (by
        rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] using h
  have houter : ContinuousOn
      (fun s : ℝ => ∫ u in (3 : ℝ)..s - 1, jurkatRichertInnerIntegral u / u)
      (Set.Icc (4 : ℝ) 6) := by
    apply hprimitive.comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change 3 ≤ s - 1 ∧ s - 1 ≤ 5
    constructor <;> linarith [hs.1, hs.2]
  have hlog : ContinuousOn (fun s : ℝ => Real.log (s - 1))
      (Set.Icc (4 : ℝ) 6) := by
    apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro s hs
    change s - 1 ≠ 0
    linarith [hs.1]
  have hfactor : ContinuousOn dimensionOneLowerLinearSieveFactor
      (Set.Icc (4 : ℝ) 6) := by
    unfold dimensionOneLowerLinearSieveFactor
    apply (continuousOn_const.div continuousOn_id ?_).mul (hlog.add houter)
    intro s hs
    change s ≠ 0
    linarith [hs.1]
  exact hfactor


/-- Continuity at Chen's ratio is an instance of the shared interval theorem. -/
theorem dimensionOneLowerLinearSieveFactor_continuousAt_five :
    ContinuousAt dimensionOneLowerLinearSieveFactor 5 :=
  dimensionOneLowerLinearSieveFactor_continuousOn_four_six.continuousAt
    (Icc_mem_nhds (by norm_num) (by norm_num))

end MathlibNt.SieveTheory.SwitchingPrinciple
