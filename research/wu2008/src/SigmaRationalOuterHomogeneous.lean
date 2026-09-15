import SigmaVariableOuterConsumer

noncomputable section
namespace SigmaRationalOuterFTC
open Real TerminalE Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open F1FullRecoveryPayment

/-- Homogenized original quadratic, not an asserted factorization over the reals. -/
def qHom (n d : ℝ) : ℝ := n^2+8*n*d+d^2

def lowerDen (n d : ℝ) : ℝ := n^2*(n+d)^4*qHom n d

def lowerNum (n d : ℝ) : ℝ :=
  k*lowerDen n d+a*d*n*(n+d)^4*qHom n d+b*d^2*(n+d)^4*qHom n d+
  c*d*n^2*(n+d)^3*qHom n d+TerminalE.d*d^2*n^2*(n+d)^2*qHom n d+
  TerminalE.e*d^3*n^2*(n+d)*qHom n d+f*d^4*n^2*qHom n d+
  (g*n*d+h*d^2)*n^2*(n+d)^4

theorem qHom_pos {n d : ℝ} (hn : 0<n) (hd : 0<d) : 0<qHom n d := by
  unfold qHom
  positivity

theorem lowerDen_pos {n d : ℝ} (hn : 0<n) (hd : 0<d) : 0<lowerDen n d := by
  exact mul_pos (mul_pos (sq_pos_of_pos hn) (pow_pos (add_pos hn hd) 4)) (qHom_pos hn hd)

/-- The unchanged complete lower envelope, after clearing its forced denominator. -/
theorem lower_homogeneous {n d : ℝ} (hd : 0<d) (hn : d≤n) :
    RemainingHf.basicLower (n/d)=lowerNum n d/lowerDen n d := by
  have hn0 : 0<n := hd.trans_le hn
  have hnd : n+d ≠ 0 := (add_pos hn0 hd).ne'
  have hq : qHom n d ≠ 0 := (qHom_pos hn0 hd).ne'
  rw [TerminalE.basic_partial ((one_le_div hd).mpr hn)]
  have he : q (n/d)=qHom n d/d^2 := by
    unfold q qHom
    field_simp
  unfold basicPartial
  rw [he]
  unfold lowerNum lowerDen
  field_simp [hn0.ne',hd.ne',hnd,hq]

/-- This extra d is necessary: the original upper envelope has a polynomial part. -/
def upperDen (n d : ℝ) : ℝ := 210*n^2*d*(n+d)^4

def upperNum (n d : ℝ) : ℝ :=
  21*n*(n-d)*(n^2+10*n*d+d^2)*(n+d)^3+
  168*n^2*d*(n-d)*(n+d)^3+56*n^2*d*(n-d)^3*(n+d)-3*(n-d)^7

theorem upperDen_pos {n d : ℝ} (hn : 0<n) (hd : 0<d) : 0<upperDen n d := by
  unfold upperDen
  positivity

theorem upper_homogeneous {n d : ℝ} (hn : 0<n) (hd : 0<d) :
    RemainingHf.basicUpper (n/d)=upperNum n d/upperDen n d := by
  have hnd : n+d ≠ 0 := (add_pos hn hd).ne'
  unfold RemainingHf.basicUpper V lowerLog upperLog upperGapPayment upperNum upperDen
  field_simp [hn.ne',hd.ne',hnd]
  ring

/-- The left split produces a new homogeneous quadratic in the original numerator and denominator. -/
theorem qHom_left (n d : ℝ) : qHom (n+d) (2*d)=n^2+18*n*d+21*d^2 := by
  unfold qHom
  ring

/-- The right split has a different forced homogeneous quadratic. -/
theorem qHom_right (n d : ℝ) : qHom (2*n) (n+d)=21*n^2+18*n*d+d^2 := by
  unfold qHom
  ring

end SigmaRationalOuterFTC
