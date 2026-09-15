import TerminalEPartial

noncomputable section
namespace TerminalE
open Real

def residue (p : ℝ) : ℝ := (g*p+h)/q p
def mainCoeff (p : ℝ) : ℝ := k+a/p+b/p^2+c/(p+1)+d/(p+1)^2+
  e/(p+1)^3+f/(p+1)^4+residue p
def zeroOne (p : ℝ) : ℝ := -a/p-b/p^2
def zeroTwo (p : ℝ) : ℝ := -b/p
def negOne (p : ℝ) : ℝ := -c/(p+1)-d/(p+1)^2-e/(p+1)^3-f/(p+1)^4
def negTwo (p : ℝ) : ℝ := -d/(p+1)-e/(p+1)^2-f/(p+1)^3
def negThree (p : ℝ) : ℝ := -e/(p+1)-f/(p+1)^2
def negFour (p : ℝ) : ℝ := -f/(p+1)
def quadOne (p : ℝ) : ℝ := -residue p
def quadZero (p : ℝ) : ℝ := g-residue p*(p+8)

def dividedPartial (p x : ℝ) : ℝ := mainCoeff p/(x-p)+zeroOne p/x+zeroTwo p/x^2+
  negOne p/(x+1)+negTwo p/(x+1)^2+negThree p/(x+1)^3+negFour p/(x+1)^4+
  (quadOne p*x+quadZero p)/q x

theorem pole_division (A B C D p x : ℝ) (hp : p ≠ 0) (hx : x ≠ 0) (hxp : x-p ≠ 0) :
    (A/x+B/x^2+C/x^3+D/x^4)/(x-p) =
      (A/p+B/p^2+C/p^3+D/p^4)/(x-p)+
      (-A/p-B/p^2-C/p^3-D/p^4)/x+
      (-B/p-C/p^2-D/p^3)/x^2+(-C/p-D/p^2)/x^3+(-D/p)/x^4 := by
  field_simp
  ring

theorem quadratic_division (p x : ℝ) (hp : q p ≠ 0) (hx : q x ≠ 0) (hxp : x-p ≠ 0) :
    ((g*x+h)/q x)/(x-p)=residue p/(x-p)+(quadOne p*x+quadZero p)/q x := by
  unfold residue quadOne quadZero
  unfold residue
  unfold q at *
  have hp' : p*(p+8)+1 ≠ 0 := by convert hp using 1; ring
  have hx' : x*(x+8)+1 ≠ 0 := by convert hx using 1; ring
  field_simp [hp', hx']
  ring

/-- Division by a forced pole preserves every principal part. -/
theorem divided_partial {p x : ℝ} (hp : 0 < p) (hx : 1 ≤ x) (hxp : x-p ≠ 0) :
    RemainingHf.basicLower x/(x-p)=dividedPartial p x := by
  have hp1 : p+1 ≠ 0 := by positivity
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hqp : q p ≠ 0 := by unfold q; positivity
  have hqx : q x ≠ 0 := by unfold q; positivity
  have hz := pole_division a b 0 0 p x hp.ne' hx0 hxp
  have hn := pole_division c d e f (p+1) (x+1) hp1 hx1
    (by simpa only [add_sub_add_right_eq_sub] using hxp)
  have hq := quadratic_division p x hqp hqx hxp
  rw [basic_partial hx]
  dsimp [basicPartial,dividedPartial,mainCoeff,zeroOne,zeroTwo,negOne,negTwo,negThree,negFour]
  simp only [add_sub_add_right_eq_sub,zero_div,add_zero,sub_zero] at hz hn
  simp only [add_div]
  linear_combination hz+hn+hq

end TerminalE
