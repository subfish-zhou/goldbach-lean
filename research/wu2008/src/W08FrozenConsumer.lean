import W08Envelope
import Wu04BypassActual

namespace WuTarget.W08
open ActualNineFeedback NodeExtension
open scoped BigOperators

theorem v8_apply_strict (i : Fin 9) :
    (∑ k : Fin 9, Wu04Bypass.elementaryMatrix i k * Wu04Bypass.v8 k) <
      (∑ k : Fin 9, paidMatrix i k * Wu04Bypass.v8 k) :=
  apply_strict Wu04Bypass.v8_nonneg ⟨0, Wu04Bypass.new_vector_positive 0⟩ i

theorem v8_apply_le_feedback (i : Fin 9) :
    (∑ k : Fin 9, paidMatrix i k * Wu04Bypass.v8 k) ≤ feedback Wu04Bypass.v8 i :=
  paidMatrix_apply_le_feedback Wu04Bypass.v8_nonneg i

theorem v8_actual_consumer :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
        base i - deltaLoss δ * loss i +
          (∑ k : Fin 9, paidMatrix i k * Wu04Bypass.v8 k) ≤ actualNine δ i := by
  obtain ⟨d, hd, hcap, hv⟩ := Wu04Bypass.new_nine_actual
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr i
  exact paidMatrix_apply_le_actual hδ (hr.trans hcap) Wu04Bypass.v8_nonneg
    (hv δ hδ hr) i

end WuTarget.W08
