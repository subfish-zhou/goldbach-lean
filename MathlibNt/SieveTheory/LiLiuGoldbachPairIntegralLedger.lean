module

public import Mathlib.Topology.Order.LeftRight
public import MathlibNt.SieveTheory.LiLiuGoldbachG67ActualIntegral
public import MathlibNt.SieveTheory.LiLiuGoldbachG67IdealNormalization
public import MathlibNt.SieveTheory.LiLiuGoldbachG67NormalizedLower
public import MathlibNt.SieveTheory.LiLiuGoldbachS5PaperSplitUpper
public import MathlibNt.SieveTheory.LiLiuGoldbachWeightAllRetainedEndpointsConsumed
public import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughPaid
public import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP
public import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDistribution


@[expose] public section

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Choose the density tolerance before epsilon and N, paying all truncation losses. -/
theorem exists_goldbachG67_integral_tolerance (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 53/(2*Real.exp Real.eulerMascheroniConstant) ∧
      goldbachG67IntegralConstant - δ ≤
        (53/(2*Real.exp Real.eulerMascheroniConstant)-ρ)*
          (goldbachG67JRIntegral 0 - (2*ρ)*goldbachG67LogRectangleMass - ρ) := by
  let k : ℝ := 53/(2*Real.exp Real.eulerMascheroniConstant)
  let f : ℝ → ℝ := fun ρ => (k-ρ)*(goldbachG67JRIntegral 0 - (2*ρ)*goldbachG67LogRectangleMass - ρ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hcont : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have he := hcont.eventually (lt_mem_nhds (sub_lt_self (f 0) hδ))
  obtain ⟨ρ,hρ,hρk,hf⟩ := ((eventually_lt_nhds hk).and he).exists_gt
  refine ⟨ρ,hρ,hρk,?_⟩
  change k*goldbachG67JRIntegral 0 - δ ≤ f ρ
  simpa [f] using hf.le


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
