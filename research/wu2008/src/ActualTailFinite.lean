import TailFTCAB11
import TailFTCAB12
import TailFTCAB21
import TailFTCAB22
import TailFTCBA11
import TailFTCBA12
import TailFTCBA21
import TailFTCBA22
noncomputable section
open Real Set MeasureTheory
open scoped Interval
namespace ActualTailFinite
open TailFiniteFTC

def kernel (u : ℝ) : ℝ := AB11.kernel u+AB12.kernel u+AB21.kernel u+AB22.kernel u+BA11.kernel u+BA12.kernel u+BA21.kernel u+BA22.kernel u
def primitive (u : ℝ) : ℝ := AB11.primitive u+AB12.primitive u+AB21.primitive u+AB22.primitive u+BA11.primitive u+BA12.primitive u+BA21.primitive u+BA22.primitive u
def mass : ℝ := AB11.mass+AB12.mass+AB21.mass+AB22.mass+BA11.mass+BA12.mass+BA21.mass+BA22.mass

theorem density_exact {u : ℝ} (hu : 2 ≤ u) : ActualTailConsumption.density u=kernel u := by
  unfold kernel
  rw [←AB11.source_exact hu,←AB12.source_exact hu,←AB21.source_exact hu,←AB22.source_exact hu,←BA11.source_exact hu,←BA12.source_exact hu,←BA21.source_exact hu,←BA22.source_exact hu]
  unfold ActualTailConsumption.density
  rw [ActualTailConsumption.retained_eq,ActualTailConsumption.retained_eq]
  unfold ActualTailConsumption.splitFloor F1JointSplit.splitLow FreshRemainingFactors.ratio
  rw [show (1327:ℝ)/200-1=1127/200 by norm_num]
  have ha : 1+(u-1)=u := by ring
  have h1 : (1+(1127/200)/(u+1))/2=((1127/200)+u+1)/(2*(u+1)) := by
    have hu1 : u+1 ≠ 0 := by linarith
    field_simp
    ring
  have h2 : 2*((1127/200)/(u+1))/(1+(1127/200)/(u+1))=
      (2*(1127/200))/((1127/200)+u+1) := by
    have hu1 : 0<u+1 := by linarith
    field_simp (disch := positivity)
    ring
  rw [ha,h1,h2]
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := AB11.primitive_deriv hu
  have h1 := AB12.primitive_deriv hu
  have h2 := AB21.primitive_deriv hu
  have h3 := AB22.primitive_deriv hu
  have h4 := BA11.primitive_deriv hu
  have h5 := BA12.primitive_deriv hu
  have h6 := BA21.primitive_deriv hu
  have h7 := BA22.primitive_deriv hu
  exact (((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7)

theorem mass_exact : ActualTailConsumption.mass=mass := by
  have hi : (∫ u in (2:ℝ)..(927/200),ActualTailConsumption.density u)=primitive (927/200)-primitive 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
      rw [density_exact hu.1]
      exact primitive_deriv hu.1
    · exact ActualTailConsumption.density_continuous.intervalIntegrable_of_Icc (by norm_num)
  change (∫ u in (2:ℝ)..(927/200),ActualTailConsumption.density u)=mass
  rw [hi]
  unfold primitive mass AB11.mass AB12.mass AB21.mass AB22.mass BA11.mass BA12.mass BA21.mass BA22.mass
  ring

def paid : ℝ := WholeCommonLog.lower+TailEndpointPayment.recovery+mass

theorem paid_exact : paid=TailEndpointPayment.paid := by
  unfold paid TailEndpointPayment.paid
  rw [mass_exact]

theorem original_firstMain_lower : 8*paid ≤ Wu08TerminalAlignment.firstMain := by
  rw [paid_exact]
  exact TailEndpointPayment.paid_le_actual

theorem strict_improvement : WholeCommonLog.lower < paid := by
  rw [paid_exact]
  exact TailEndpointPayment.strict_improvement
end ActualTailFinite
