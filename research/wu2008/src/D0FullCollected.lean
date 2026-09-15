import D0FullProfile

noncomputable section
namespace D0FullDensity
open Real TerminalE TerminalESigned
local notation "te" => TerminalE.e

def zeroMain : ℝ := k+c+d+te+f+h
def zeroNeg : ℝ := -c-d-te-f
def zeroMinus : ℝ := -h/2+(g-4*h)/(2*radical)
def zeroPlus : ℝ := -h/2-(g-4*h)/(2*radical)
def zeroRational (x : ℝ) : ℝ := -a/x-b/(2*x^2)-(-d-te-f)/(x+1)-(-te-f)/(2*(x+1)^2)+f/(3*(x+1)^3)

theorem zero_expansion {x : ℝ} (hx : 1≤x) :
    zeroPrimitive x=zeroRational x+zeroMain*log x+zeroNeg*log (x+1)+
      zeroMinus*log (x+4-radical)+zeroPlus*log (x+4+radical) := by
  unfold zeroPrimitive
  rw [quadratic_split hx]
  unfold zeroRational zeroMain zeroNeg zeroMinus zeroPlus FirstCRationalPayment.polePrimitive
  simp only [sub_zero,sub_neg_eq_add]
  ring

def leftMinus (v : ℝ) : ℝ := (9-2*radical)*v-5+2*radical
def leftPlus (v : ℝ) : ℝ := (9+2*radical)*v-5-2*radical
def rightMinus (v : ℝ) : ℝ := (4-radical)*v+20-3*radical
def rightPlus (v : ℝ) : ℝ := (4+radical)*v+20+3*radical

theorem affine_positive {v : ℝ} (hv : 3≤v) :
    0<leftMinus v ∧ 0<leftPlus v ∧ 0<rightMinus v ∧ 0<rightPlus v := by
  have hm : 0<9-2*radical := by linarith only [radical_lt_four]
  have hp : 0<9+2*radical := by linarith only [radical_pos]
  have hmr : 0<4-radical := by linarith only [radical_lt_four]
  have hpr : 0<4+radical := by linarith only [radical_pos]
  dsimp [leftMinus,leftPlus,rightMinus,rightPlus]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [mul_nonneg hm.le (sub_nonneg.mpr hv),radical_lt_four]
  · nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hv),radical_pos]
  · nlinarith only [mul_nonneg hmr.le (sub_nonneg.mpr hv),radical_lt_four]
  · nlinarith only [mul_nonneg hpr.le (sub_nonneg.mpr hv),radical_pos]

theorem left_logs {v : ℝ} (hv : 3≤v) :
    log (leftArg v-(-3/2))=log v-log (v-1)+log 2 ∧
    log (leftArg v-1/2)=log 2-log (v-1) ∧
    log (leftArg v)=log (v+3)-log (v-1)-log 2 ∧
    log (leftArg v+1)=log (3*v+1)-log (v-1)-log 2 ∧
    log (leftArg v+4-radical)=log (leftMinus v)-log (v-1)-log 2 ∧
    log (leftArg v+4+radical)=log (leftPlus v)-log (v-1)-log 2 := by
  have hv0 : v ≠ 0 := by linarith
  have hv1 : v-1 ≠ 0 := by linarith
  have hv3 : v+3 ≠ 0 := by linarith
  have hvt : 3*v+1 ≠ 0 := by linarith
  have hh := affine_positive hv
  have h0 : leftArg v-(-3/2)=2*v/(v-1) := by unfold leftArg; field_simp; ring
  have h1 : leftArg v-1/2=2/(v-1) := by unfold leftArg; field_simp; ring
  have h2 : leftArg v+1=(3*v+1)/(2*(v-1)) := by unfold leftArg; field_simp; ring
  have hm : leftArg v+4-radical=leftMinus v/(2*(v-1)) := by unfold leftArg leftMinus; field_simp; ring
  have hp : leftArg v+4+radical=leftPlus v/(2*(v-1)) := by unfold leftArg leftPlus; field_simp; ring
  rw [h0,h1,h2,hm,hp]
  unfold leftArg
  rw [log_div (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv0) hv1,
    log_mul (by norm_num : (2:ℝ) ≠ 0) hv0,
    log_div (by norm_num : (2:ℝ) ≠ 0) hv1,
    log_div hv3 (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv1),
    log_div hvt (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv1),
    log_div hh.1.ne' (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv1),
    log_div hh.2.1.ne' (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv1),
    log_mul (by norm_num : (2:ℝ) ≠ 0) hv1]
  refine ⟨by ring,rfl,by ring,by ring,by ring,by ring⟩

theorem right_logs {v : ℝ} (hv : 3≤v) :
    log (rightArg v-8/3)=log v-log (v+3)+log (8/3) ∧
    log (rightArg v)=log 8-log (v+3) ∧
    log (rightArg v+1)=log (v+11)-log (v+3) ∧
    log (rightArg v+4-radical)=log (rightMinus v)-log (v+3) ∧
    log (rightArg v+4+radical)=log (rightPlus v)-log (v+3) := by
  have hv0 : v ≠ 0 := by linarith
  have hv3 : v+3 ≠ 0 := by linarith
  have hv11 : v+11 ≠ 0 := by linarith
  have hh := affine_positive hv
  have h0 : rightArg v-8/3= -((8/3)*v/(v+3)) := by unfold rightArg; field_simp; ring
  have h1 : rightArg v+1=(v+11)/(v+3) := by unfold rightArg; field_simp; ring
  have hm : rightArg v+4-radical=rightMinus v/(v+3) := by unfold rightArg rightMinus; field_simp; ring
  have hp : rightArg v+4+radical=rightPlus v/(v+3) := by unfold rightArg rightPlus; field_simp; ring
  rw [h0,h1,hm,hp,log_neg_eq_log,
    log_div (mul_ne_zero (by norm_num : (8/3:ℝ) ≠ 0) hv0) hv3,
    log_mul (by norm_num : (8/3:ℝ) ≠ 0) hv0,
    log_div hv11 hv3,log_div hh.2.2.1.ne' hv3,log_div hh.2.2.2.ne' hv3]
  unfold rightArg
  rw [log_div (by norm_num : (8:ℝ) ≠ 0) hv3]
  exact ⟨by ring,rfl,rfl,rfl,rfl⟩

def coeffV : ℝ := mainCoeff (-3/2)+mainCoeff (8/3)
def coeffMinusOne : ℝ := -mainCoeff (-3/2)+mainCoeff (1/2)-
  (zeroOne (-3/2)-zeroOne (1/2))-(negOne (-3/2)-negOne (1/2))-
  (minusCoeff (-3/2)-minusCoeff (1/2))-(plusCoeff (-3/2)-plusCoeff (1/2))
def coeffPlusThree : ℝ := zeroOne (-3/2)-zeroOne (1/2)-mainCoeff (8/3)-zeroOne (8/3)+zeroMain-
  (negOne (8/3)-zeroNeg)-(minusCoeff (8/3)-zeroMinus)-(plusCoeff (8/3)-zeroPlus)
def coeffTriple : ℝ := negOne (-3/2)-negOne (1/2)
def coeffEleven : ℝ := negOne (8/3)-zeroNeg

def rationalFull (v : ℝ) : ℝ := rationalPart (-3/2) (leftArg v)-rationalPart (1/2) (leftArg v)+
  rationalPart (8/3) (rightArg v)-zeroRational (rightArg v)
def affineLogs (v : ℝ) : ℝ := coeffV*log v+coeffMinusOne*log (v-1)+
  coeffPlusThree*log (v+3)+coeffTriple*log (3*v+1)+coeffEleven*log (v+11)+
  (minusCoeff (-3/2)-minusCoeff (1/2))*log (leftMinus v)+
  (plusCoeff (-3/2)-plusCoeff (1/2))*log (leftPlus v)+
  (minusCoeff (8/3)-zeroMinus)*log (rightMinus v)+
  (plusCoeff (8/3)-zeroPlus)*log (rightPlus v)
def constantLog : ℝ := (mainCoeff (-3/2)-mainCoeff (1/2)-(zeroOne (-3/2)-zeroOne (1/2))-
  (negOne (-3/2)-negOne (1/2))-(minusCoeff (-3/2)-minusCoeff (1/2))-
  (plusCoeff (-3/2)-plusCoeff (1/2)))*log 2+mainCoeff (8/3)*log (8/3)+(zeroOne (8/3)-zeroMain)*log 8

theorem fullPrimitive_collected {v : ℝ} (hv : 3≤v) (hv5 : v≤5) :
    fullPrimitive v=rationalFull v+affineLogs v+constantLog := by
  have hb := argument_bounds hv hv5
  obtain ⟨l0,l1,l2,l3,l4,l5⟩ := left_logs hv
  obtain ⟨r0,r1,r2,r3,r4⟩ := right_logs hv
  unfold fullPrimitive
  rw [primitive_expansion hb.1,primitive_expansion hb.1,
    primitive_expansion hb.2.2.2.1,zero_expansion hb.2.2.2.1]
  rw [l0,l1,l2,l3,l4,l5,r0,r1,r2,r3,r4]
  unfold rationalFull affineLogs constantLog coeffV coeffMinusOne coeffPlusThree coeffTriple coeffEleven
  ring

theorem fullMass_collected : fullMass=rationalFull 5-rationalFull 3+affineLogs 5-affineLogs 3 := by
  unfold fullMass
  rw [fullPrimitive_collected (by norm_num) le_rfl,fullPrimitive_collected le_rfl (by norm_num)]
  ring

end D0FullDensity
