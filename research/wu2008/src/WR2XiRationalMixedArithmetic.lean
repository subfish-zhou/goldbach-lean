import WR2XiRationalMixedCell00
import WR2XiRationalMixedCell01
import WR2XiRationalMixedCell02
import WR2XiRationalMixedCell03
import WR2XiRationalMixedCell04
import WR2XiRationalMixedCell10
import WR2XiRationalMixedCell11
import WR2XiRationalMixedCell12
import WR2XiRationalMixedCell13
import WR2XiRationalMixedCell20
import WR2XiRationalMixedCell21
import WR2XiRationalMixedCell22
import WR2XiRationalMixedCell23
import WR2XiRationalMixedCell30
namespace Xi2RationalMixed
open Xi2RationalTop
theorem mixed_arithmetic : ∀ r k, left k < factors r 1 - 1 →
    target r k + (if k = 0 then debit r else 0) ≤ entry r k := by
  intro r k h
  fin_cases r <;> fin_cases k <;> first
    | exact mixed_0_0
    | exact mixed_0_1
    | exact mixed_0_2
    | exact mixed_0_3
    | exact mixed_0_4
    | exact mixed_1_0
    | exact mixed_1_1
    | exact mixed_1_2
    | exact mixed_1_3
    | exact mixed_2_0
    | exact mixed_2_1
    | exact mixed_2_2
    | exact mixed_2_3
    | exact mixed_3_0 
    | norm_num [left, factors] at h
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_arithmetic
