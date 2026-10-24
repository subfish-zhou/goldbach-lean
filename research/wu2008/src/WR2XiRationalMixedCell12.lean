import WR2XiRationalMixedData
namespace Xi2RationalMixed
open Xi2RationalTop
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_1_2 : target 1 2 + (if (2 : Fin 9) = 0 then debit 1 else 0) ≤ entry 1 2 := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_1_2
