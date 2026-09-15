import SigmaRemainingOriginal

noncomputable section
namespace TerminalE
open Real Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment

def q (x : ℝ) : ℝ := x^2+8*x+1
def k : ℝ := 155/42
def a : ℝ := 64/105
def b : ℝ := -1/30
def c : ℝ := -128/105
def d : ℝ := -64/945
def e : ℝ := 128/315
def f : ℝ := 64/315
def g : ℝ := -500/21
def h : ℝ := -10*(k+a+b+c/2+d/4+e/8+f/16)-g

def basicPartial (x : ℝ) : ℝ :=
  k+a/x+b/x^2+c/(x+1)+d/(x+1)^2+e/(x+1)^3+f/(x+1)^4+(g*x+h)/q x

/-- Exact principal parts forced by the existing complete lower envelope. -/
theorem basic_partial {x : ℝ} (hx : 1 ≤ x) : RemainingHf.basicLower x=basicPartial x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hq : q x ≠ 0 := by unfold q; positivity
  simp only [RemainingHf.basicLower, lowerGapPayment, lowerLog, upperLog,
    F1LowerResidual.payment, F1LowerResidual.denom, basicPartial, h, k, a, b, c, d, e, f, g, q] at *
  field_simp
  ring

end TerminalE
