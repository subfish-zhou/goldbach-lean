import WE02JointCreditRankOneRows

namespace WuTarget.E02JointCredit
open ActualNineFeedback NodeExtension

def rankOneTransferLower : Fin 21 → ℚ :=
  ![320758699/1000000000000, 151851393/500000000000,
    286646873/1000000000000, 3369887/12500000000,
    252535047/1000000000000, 117739567/500000000000,
    218423221/1000000000000, 50341827/250000000000,
    36862279/200000000000, 83627741/500000000000,
    150199569/1000000000000, 16642957/125000000000,
    116501257/1000000000000, 3145411/31250000000,
    84747207/1000000000000, 69097793/1000000000000,
    54307507/1000000000000, 1613051/40000000000,
    5431547/200000000000, 1489101/100000000000,
    12305207/1000000000000]

theorem rankOneTransferLower_pos (j : Fin 21) : 0 < rankOneTransferLower j := by
  fin_cases j <;> norm_num [rankOneTransferLower]

theorem rankOneTransferLower_le_q (j : Fin 21) :
    rankOneTransferLower j ≤ rankOneQTransfer j := by
  fin_cases j <;> decide +kernel

theorem rankOneTransferLower_le_rational (j : Fin 21) :
    (rankOneTransferLower j : ℝ) ≤
      matrixApply W02.rationalMatrix difference j := by
  have h : (rankOneTransferLower j : ℝ) ≤ (rankOneQTransfer j : ℝ) := by
    exact_mod_cast rankOneTransferLower_le_q j
  exact h.trans (rankOneQTransfer_le j)

theorem rankOneTransferLower_le_actual (j : Fin 21) :
    (rankOneTransferLower j : ℝ) ≤ transferredDifference j := by
  apply (rankOneTransferLower_le_rational j).trans
  exact W02.apply_lower difference_nonneg j

end WuTarget.E02JointCredit
