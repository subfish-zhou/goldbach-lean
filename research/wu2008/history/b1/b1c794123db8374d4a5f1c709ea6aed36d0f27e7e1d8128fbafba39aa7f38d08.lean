import SrcFifthGainStaircase

namespace WuSource.SrcFifthGain
open MeasureTheory Set Real
#check @Antitone.intervalIntegrable
#check @IntervalIntegrable.mul_continuousOn
#check @MeasureTheory.IntegrableOn.of_bound
#check @intervalIntegrable_iff_integrableOn_Icc_of_le
#check @intervalIntegral.integral_finsetSum
#check @Finset.sum_Ico_eq_sum_range
#check @MeasureTheory.Integrable.integrableOn
#check @Wu2008DoubleSieve.fifthPair_Fdelta_right_limit
#check @Metric.tendsto_nhdsWithin_nhds
end WuSource.SrcFifthGain
