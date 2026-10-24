import WR2XiRationalMixedData
namespace Xi2RationalMixed
open Xi2RationalTop
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_0_3 : target 0 3 + (if (3 : Fin 9) = 0 then debit 0 else 0) ≤ entry 0 3 := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_0_3
