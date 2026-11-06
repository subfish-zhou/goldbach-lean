import InsertedGainCover
import HighO2TerminalQuadrature

namespace CoverMass
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology Interval
noncomputable section

/-- The existing exact substitution at the constant coefficient, including s=2. -/
theorem kernel_exact {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    (∫ u in (1-1/s)..(1-1/t), (1 : ℝ)/(u*(1-u))) = log ((t-1)/(s-1)) := by
  rw [← omega2_integral_substitution (fun _ => (1 : ℝ)) hs hst]
  exact integral_one_div_of_pos (by linarith) (by linarith)


end
end CoverMass
