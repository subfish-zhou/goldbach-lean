import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveAmplitudeLimit

/-!
# The finite lower-boundary constant and its real limit

This module records the unconditional consequences of the already proved real
summability.  It does not assume or define Suzuki's source normalization `B=0`.
-/

open scoped Classical BigOperators
open Filter Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The real limiting lower-boundary constant at `κ=1, β=2`. -/
noncomputable def suzukiLowerBoundaryLimit : ℝ :=
  2 * (1 - suzukiEvenSourceLowerLayerLimit 2)

/-- The finite constants `B_m=2(1-T_{2m}(2))` decrease with depth. -/
theorem antitone_suzukiFiniteLowerBoundary : Antitone suzukiFiniteLowerBoundary := by
  intro m n hmn
  unfold suzukiFiniteLowerBoundary
  have hmono := suzukiEvenSourceLowerPartialSum_monotone (s := (2 : ℝ)) (by norm_num)
  have hle := hmono hmn
  linarith

/-- Exact finite normalization `2*T_{2m}(2)=2-B_m`. -/
theorem suzuki_finite_lower_normalization (m : ℕ) :
    2 * suzukiEvenSourceLowerPartialSum m 2 =
      2 - suzukiFiniteLowerBoundary m := by
  unfold suzukiFiniteLowerBoundary
  ring

/-- The finite boundary constants converge in `ℝ` to their genuine series
normalization. -/
theorem tendsto_suzukiFiniteLowerBoundary
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiFiniteLowerBoundary atTop (𝓝 suzukiLowerBoundaryLimit) := by
  have hmass := tendsto_suzukiEvenSourceLowerPartialSum_real hH
    (s := (2 : ℝ)) (by norm_num)
  unfold suzukiFiniteLowerBoundary suzukiLowerBoundaryLimit
  simpa only [] using ((tendsto_const_nhds.sub hmass).const_mul (2 : ℝ))

/-- Suzuki's `B=0` is exactly normalization of the even lower mass to one. -/
theorem suzukiLowerBoundaryLimit_eq_zero_iff :
    suzukiLowerBoundaryLimit = 0 ↔ suzukiEvenSourceLowerLayerLimit 2 = 1 := by
  unfold suzukiLowerBoundaryLimit
  constructor <;> intro h <;> linarith


end MathlibNt.SieveTheory
