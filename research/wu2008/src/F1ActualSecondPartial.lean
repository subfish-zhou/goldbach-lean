import F1JointSplitCount

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open scoped Interval
namespace F1ActualSecondFTC

def coeffA : ℝ := (1854:ℝ)/1327
def coeffB : ℝ := (-1413349322907361444:ℝ)/99077443529748784087
def coeffC : ℝ := (11219157004384:ℝ)/6810904305621
def coeffD : ℝ := (-1842092960:ℝ)/4663938123
def coeffE : ℝ := (304768:ℝ)/3193749
def coeffF : ℝ := (-169702300:ℝ)/2663823
def coeffG : ℝ := (458672800:ℝ)/7991469

def kernel (u : ℝ) : ℝ :=
  2*momentWeight u/(u*(u+1327/200)*(3*u-2)^3*(21*u^2-24*u+4))

def partialKernel (u : ℝ) : ℝ :=
  coeffA/u+coeffB/(u+1327/200)+coeffC/(u-2/3)+coeffD/(u-2/3)^2+
    coeffE/(u-2/3)^3+(coeffF*u+coeffG)/(21*u^2-24*u+4)

theorem denominator_pos {u : ℝ} (hu : 2 ≤ u) :
    0 < u*(u+1327/200)*(3*u-2)^3*(21*u^2-24*u+4) := by
  have hu0 : 0 < u := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  positivity

theorem kernel_partial {u : ℝ} (hu : 2 ≤ u) : kernel u = partialKernel u := by
  have hu0 : u ≠ 0 := by linarith
  have hs : u+1327/200 ≠ 0 := by linarith
  have ht : 3*u-2 ≠ 0 := by linarith
  have hp : u-2/3 ≠ 0 := by linarith
  have hq : 21*u^2-24*u+4 ≠ 0 := by
    have h : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
    exact h.ne'
  unfold kernel partialKernel momentWeight coeffA coeffB coeffC coeffD coeffE coeffF coeffG
  rw [show 3*u-2=3*(u-2/3) by ring]
  have hn3 : u*3-2 ≠ 0 := by linarith
  have hnq : u*(u*21-24)+4 ≠ 0 := by
    convert hq using 1
    ring
  field_simp [hu0,hs,hp,hq,hn3,hnq]
  ring

end F1ActualSecondFTC
