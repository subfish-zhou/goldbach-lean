import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.FunProp

/-! Global measure instances and Fourier continuity registrations.
These registrations retain the environment used by existing downstream proofs.
The mathematical PNT bridge is proved separately. -/

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal
