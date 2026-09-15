import HighIncrementTerminal
import LowComplementConsumer

namespace MixedFinal
open Wu2008DoubleSieve Filter
open scoped Topology
noncomputable section

/-- The independent high-lane result discharges the exact remaining binder. -/
theorem normalization {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (truncatedSixthLowerF6lin+FeedbackLimit.Cinf+HighConsumer.highGain-ε)*
          truncatedSixthMassScale N ≤ MixedSixth.main N n δ η := by
  apply LowComplement.combine_with_high_payment ?_ hε
  intro e he
  obtain ⟨d,hd,h⟩ := HighIncrement.actual_highGain_lower he
  refine ⟨d,hd,?_⟩
  intro δ hδ hδd
  obtain ⟨n0,hn⟩ := h δ hδ.le hδd.le
  exact eventually_atTop.mpr ⟨n0,hn⟩

end
end MixedFinal
