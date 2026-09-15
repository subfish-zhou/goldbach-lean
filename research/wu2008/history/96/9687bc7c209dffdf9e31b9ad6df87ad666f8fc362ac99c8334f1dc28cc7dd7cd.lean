import WE07FifthSourceRoot
import PositiveCoreFifth

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve MeasureTheory Set Real
set_option pp.fullNames true
#print fifthH_actual_Fdelta_lower
#print fifthH_actual_integral_split
#print fifthHOnlyKernel
#print fifthHOnlyIntegral
#print fifthH_denominator_bounds
#print fifthH_only_integrable
#print fifthPairCount
#print fifthPairRegion
#print fifthPair_Fdelta_close
#print wuImprovementLimit_lower_antitone
#print wuImprovementLimit_nonneg
#print wuImprovementLimit
#print axioms fifthH_actual_Fdelta_lower
#check @Integrable.mono'
#check @Integrable.bdd_mul
#check @MeasureTheory.integral_finset_sum
#check @intervalIntegral.sum_integral_adjacent_intervals
#check @MeasureTheory.integral_indicator
#check @MeasureTheory.integral_Ioc_eq_integral_Icc
end WuSource.SrcFifthGain
