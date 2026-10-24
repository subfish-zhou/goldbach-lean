import WR2XiRationalMixedData
namespace Xi2RationalMixed
open Xi2RationalTop
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_2_2 : target 2 2 + (if (2 : Fin 9) = 0 then debit 2 else 0) ≤ entry 2 2 := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_2_2
