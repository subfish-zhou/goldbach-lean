import W15AcceptedCount

namespace WuTarget.W15Accepted

theorem paid_threshold_iff (x : Fin 9 → ℝ) :
    (4491/5000 : ℝ) ≤ paidCoefficient x ↔
      (3590307/4000000 : ℝ) ≤ remainingCoefficient x := by
  unfold paidCoefficient
  constructor <;> intro h <;> linarith

end WuTarget.W15Accepted

#check @WuTarget.W15Accepted.paid_threshold_iff
#print axioms WuTarget.W15Accepted.paid_threshold_iff
