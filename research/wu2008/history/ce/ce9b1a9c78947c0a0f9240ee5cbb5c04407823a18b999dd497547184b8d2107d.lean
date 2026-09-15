import WE07FifthSourceRoot
import PositiveCoreFifth

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve MeasureTheory Set Real
set_option pp.fullNames true
#check @fifthH_actual_Fdelta_lower
#check @fifthH_actual_integral_split
#print fifthHOnlyKernel
#print fifthHOnlyIntegral
#check @fifthH_denominator_bounds
#check @fifthH_only_integrable
#print fifthPairCount
#print fifthPairRegion
#check @fifthPair_Fdelta_close
#check @wuImprovementLimit_lower_antitone
#check @wuImprovementLimit_nonneg
#print wuImprovementLimit
#print axioms fifthH_actual_Fdelta_lower
#check @Integrable.mono'
#check @Integrable.bdd_mul
#check @MeasureTheory.integral_finsetSum
#check @intervalIntegral.sum_integral_adjacent_intervals
#check @MeasureTheory.integral_indicator
#check @intervalIntegral.integral_of_le
#check @MeasureTheory.IntegrableOn.mono_set
end WuSource.SrcFifthGain
