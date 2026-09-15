import SigmaRationalOuterHomogeneous

noncomputable section
namespace SigmaRationalOuterFTC
open Real Wu04FactorEnvelopes

/-- The two existing factors are retained separately in the complete denominator. -/
def splitLowerDen (n d : ℝ) : ℝ := lowerDen (n+d) (2*d)*lowerDen (2*n) (n+d)
def splitLowerNum (n d : ℝ) : ℝ :=
  lowerNum (n+d) (2*d)*lowerDen (2*n) (n+d)+
  lowerNum (2*n) (n+d)*lowerDen (n+d) (2*d)
def splitUpperDen (n d : ℝ) : ℝ := upperDen (n+d) (2*d)*upperDen (2*n) (n+d)
def splitUpperNum (n d : ℝ) : ℝ :=
  upperNum (n+d) (2*d)*upperDen (2*n) (n+d)+
  upperNum (2*n) (n+d)*upperDen (n+d) (2*d)

theorem split_factors {n d : ℝ} (hd : 0<d) (hn : d≤n) :
    leftFactor (n/d)=(n+d)/(2*d) ∧ rightFactor (n/d)=2*n/(n+d) := by
  have hn0 := hd.trans_le hn
  have hnd := (add_pos hn0 hd).ne'
  simp only [leftFactor,rightFactor]
  constructor <;> field_simp [hd.ne',hnd] <;> ring

theorem splitLowerDen_pos {n d : ℝ} (hn : 0<n) (hd : 0<d) : 0<splitLowerDen n d :=
  mul_pos (lowerDen_pos (add_pos hn hd) (by positivity))
    (lowerDen_pos (by positivity) (add_pos hn hd))

theorem splitUpperDen_pos {n d : ℝ} (hn : 0<n) (hd : 0<d) : 0<splitUpperDen n d :=
  mul_pos (upperDen_pos (add_pos hn hd) (by positivity))
    (upperDen_pos (by positivity) (add_pos hn hd))

theorem splitLower_homogeneous {n d : ℝ} (hd : 0<d) (hn : d≤n) :
    RemainingHf.splitLower (n/d)=splitLowerNum n d/splitLowerDen n d := by
  obtain ⟨hl,hr⟩ := split_factors hd hn
  have hn0 := hd.trans_le hn
  unfold RemainingHf.splitLower
  rw [hl,hr,lower_homogeneous (by positivity : 0<2*d) (by linarith : 2*d≤n+d),
    lower_homogeneous (add_pos hn0 hd) (by linarith : n+d≤2*n)]
  unfold splitLowerNum splitLowerDen
  simpa only [mul_comm] using div_add_div (lowerNum (n+d) (2*d)) (lowerNum (2*n) (n+d))
    (lowerDen_pos (add_pos hn0 hd) (by positivity : 0<2*d)).ne'
    (lowerDen_pos (by positivity : 0<2*n) (add_pos hn0 hd)).ne'

theorem splitUpper_homogeneous {n d : ℝ} (hd : 0<d) (hn : d≤n) :
    RemainingHf.splitUpper (n/d)=splitUpperNum n d/splitUpperDen n d := by
  obtain ⟨hl,hr⟩ := split_factors hd hn
  have hn0 := hd.trans_le hn
  unfold RemainingHf.splitUpper
  rw [hl,hr,upper_homogeneous (add_pos hn0 hd) (by positivity : 0<2*d),
    upper_homogeneous (by positivity : 0<2*n) (add_pos hn0 hd)]
  unfold splitUpperNum splitUpperDen
  simpa only [mul_comm] using div_add_div (upperNum (n+d) (2*d)) (upperNum (2*n) (n+d))
    (upperDen_pos (add_pos hn0 hd) (by positivity : 0<2*d)).ne'
    (upperDen_pos (by positivity : 0<2*n) (add_pos hn0 hd)).ne'

/-- The numerator and denominator of the original quadratic ratio. -/
def quadN (t : ℝ) : ℝ := (t^2+18*t+21)*(t+2)^2
def quadD (t : ℝ) : ℝ := 90*(t+1)^2

/-- This is the forced left eighth-degree polynomial, with no root approximation. -/
def eighthLeft (t : ℝ) : ℝ :=
  t^8+44*t^7+2298*t^6+43460*t^5+416581*t^4+1317000*t^3+
  1859892*t^2+1231488*t+313236

/-- The other eighth-degree factor is distinct and is not dropped. -/
def eighthRight (t : ℝ) : ℝ :=
  t^8+44*t^7+(5286/7)*t^6+(45020/7)*t^5+27781*t^4+64200*t^3+
  (566844/7)*t^2+(369216/7)*t+97452/7

theorem eighthLeft_identity (t : ℝ) :
    qHom (quadN t+quadD t) (2*quadD t)=eighthLeft t := by
  unfold qHom quadN quadD eighthLeft
  ring

theorem eighthRight_identity (t : ℝ) :
    qHom (2*quadN t) (quadN t+quadD t)=21*eighthRight t := by
  unfold qHom quadN quadD eighthRight
  ring

theorem eighthLeft_pos {t : ℝ} (ht : 1≤t) : 0<eighthLeft t := by
  rw [←eighthLeft_identity]
  apply qHom_pos <;> dsimp [quadN,quadD] <;> positivity

theorem eighthRight_pos {t : ℝ} (ht : 1≤t) : 0<eighthRight t := by
  have h : 0<qHom (2*quadN t) (quadN t+quadD t) := by
    apply qHom_pos <;> dsimp [quadN,quadD] <;> positivity
  rw [eighthRight_identity] at h
  linarith only [h]

end SigmaRationalOuterFTC
