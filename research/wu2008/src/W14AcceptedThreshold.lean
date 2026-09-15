import W14AcceptedCount

namespace WuTarget.W14Accepted

theorem paid_threshold_iff (x : Fin 9 → ℝ) :
    (4491/5000 : ℝ) ≤ paidCoefficient x ↔
      (-7128233/4000000 : ℝ) ≤ remainingCoefficient x := by
  unfold paidCoefficient
  constructor <;> intro h <;> linarith

end WuTarget.W14Accepted
