import NodeTransfer
import Wu04BypassCells
import Wu04BypassActual

namespace WuTarget.W02

#check NodeExtension.transferMatrix
#check NodeExtension.originalTransfer_expansion
#check NodeExtension.weighted_profile_expansion
#check NodeExtension.nineProfile_basis
#check NodeExtension.profiles_nonneg
#check Wu04Bypass.cell_le_integral
#check Wu04Bypass.new_nine_and_twentyone_actual
#check ActualNineFeedback.matrixApply
#check intervalIntegral.integral_indicator
#check intervalIntegral.integral_of_le
#check intervalIntegral.integral_congr_uIoo
#check intervalIntegral.integral_mono_interval
#check intervalIntegral.integral_nonneg
#check NodeExtension.clip_lower
#check NodeExtension.clip_upper
#check MeasureTheory.integral_indicator

end WuTarget.W02
