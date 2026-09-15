import EJointFrontier

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open scoped Interval
namespace F1JointFTC

def partA : ℝ := (-1854:ℝ)/1327
def partB : ℝ := (69254116822460710756:ℝ)/2458221729281865711
def partC : ℝ := (-49240042304:ℝ)/2389793949
def partD : ℝ := (97066528:ℝ)/2577987
def partE : ℝ := (-169856:ℝ)/2781
def partF : ℝ := (-57004300:ℝ)/6976413
def partG : ℝ := (445565600:ℝ)/6976413

def kernel (u : ℝ) : ℝ := 2*momentWeight u/momentDenom u

def partialKernel (u : ℝ) : ℝ :=
  partA/u+partB/(u+1327/200)+partC/(u+2)+partD/(u+2)^2+partE/(u+2)^3+
    (partF*u+partG)/(u^2+16*u+4)

theorem kernel_partial {u : ℝ} (hu : 2 ≤ u) : kernel u = partialKernel u := by
  have hu0 : u ≠ 0 := by linarith
  have hs : u+1327/200 ≠ 0 := by linarith
  have hp : u+2 ≠ 0 := by linarith
  have hq : u^2+16*u+4 ≠ 0 := by positivity
  unfold kernel partialKernel momentWeight momentDenom partA partB partC partD partE partF partG
  rw [show (1327:ℝ)/200+u=u+1327/200 by ring]
  field_simp
  ring

end F1JointFTC
