import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21HorizontalDecay
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21LogDerivativeFinal

noncomputable section
open Filter Complex
open scoped Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Any fixed logarithmic growth degree is paid by the source smoothing order. -/
theorem chen1973Lemma6_eq21_order_eventually (r : ℕ) :
    ∀ᶠ x : ℕ in atTop, r + 1 ≤ chen1973PerronOrder (x : ℝ) + 1 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (r : ℝ)] with x hx
  have hfloor : r ≤ ⌊Real.log (x : ℝ)⌋₊ := Nat.le_floor hx
  simpa only [chen1973PerronOrder] using Nat.add_le_add_right hfloor 1


end AnalyticNumberTheory.LargeSieve
