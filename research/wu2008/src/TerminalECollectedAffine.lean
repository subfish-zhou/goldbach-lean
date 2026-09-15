import TerminalESignedAtoms

noncomputable section
namespace TerminalESigned
open Real TerminalE

def coeffU : ℝ := mainCoeff (3/4)+mainCoeff (2/3)
def coeffThree : ℝ := -mainCoeff (2/3)+mainCoeff 2+zeroOne (3/4)-
  (zeroOne (2/3)-zeroOne 2)-(negOne (2/3)-negOne 2)-
  (minusCoeff (2/3)-minusCoeff 2)-(plusCoeff (2/3)-plusCoeff 2)
def coeffOne : ℝ := zeroOne (2/3)-zeroOne 2
def coeffSeven : ℝ := negOne (3/4)
def coeffFive : ℝ := negOne (2/3)-negOne 2
def leftMinus (u : ℝ) : ℝ := u+19-4*radical
def leftPlus (u : ℝ) : ℝ := u+19+4*radical
def rightMinus (u : ℝ) : ℝ := (6-radical)*u+14-3*radical
def rightPlus (u : ℝ) : ℝ := (6+radical)*u+14+3*radical

def rationalFull (u : ℝ) : ℝ := rationalPart (3/4) (leftArg u)+
  rationalPart (2/3) (rightArg u)-rationalPart 2 (rightArg u)
def affineLogs (u : ℝ) : ℝ := coeffU*log u+coeffThree*log (u+3)+
  coeffOne*log (u+1)+coeffSeven*log (u+7)+coeffFive*log (3*u+5)+
  minusCoeff (3/4)*log (leftMinus u)+plusCoeff (3/4)*log (leftPlus u)+
  (minusCoeff (2/3)-minusCoeff 2)*log (rightMinus u)+
  (plusCoeff (2/3)-plusCoeff 2)*log (rightPlus u)
def constantLog : ℝ :=
  -(mainCoeff (3/4)+zeroOne (3/4)+negOne (3/4)+minusCoeff (3/4)+plusCoeff (3/4))*log 4+
  mainCoeff (2/3)*log (4/3)-mainCoeff 2*log 4+coeffOne*log 2

theorem affine_positive {u : ℝ} (hu : 1≤u) :
    0<leftMinus u ∧ 0<leftPlus u ∧ 0<rightMinus u ∧ 0<rightPlus u := by
  have hm : 0<6-radical := by linarith only [radical_lt_four]
  have hp : 0<6+radical := by linarith only [radical_pos]
  dsimp [leftMinus,leftPlus,rightMinus,rightPlus]
  constructor
  · linarith only [hu,radical_lt_four]
  constructor
  · linarith only [hu,radical_pos]
  constructor
  · nlinarith only [mul_nonneg hm.le (sub_nonneg.mpr hu),radical_lt_four]
  · nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hu),radical_pos]

theorem left_logs {u : ℝ} (hu : 1≤u) :
    log (leftArg u-3/4)=log u-log 4 ∧
    log (leftArg u)=log (u+3)-log 4 ∧
    log (leftArg u+1)=log (u+7)-log 4 ∧
    log (leftArg u+4-radical)=log (leftMinus u)-log 4 ∧
    log (leftArg u+4+radical)=log (leftPlus u)-log 4 := by
  have hu0 : u ≠ 0 := by linarith
  have hu3 : u+3 ≠ 0 := by linarith
  have hu7 : u+7 ≠ 0 := by linarith
  have hh := affine_positive hu
  have h0 : leftArg u-3/4=u/4 := by unfold leftArg; ring
  have h1 : leftArg u+1=(u+7)/4 := by unfold leftArg; ring
  have hm : leftArg u+4-radical=leftMinus u/4 := by unfold leftArg leftMinus; ring
  have hp : leftArg u+4+radical=leftPlus u/4 := by unfold leftArg leftPlus; ring
  rw [h0,h1,hm,hp]
  simp only [leftArg,log_div hu0 (by norm_num : (4:ℝ) ≠ 0),
    log_div hu3 (by norm_num : (4:ℝ) ≠ 0),log_div hu7 (by norm_num : (4:ℝ) ≠ 0),
    log_div hh.1.ne' (by norm_num : (4:ℝ) ≠ 0),
    log_div hh.2.1.ne' (by norm_num : (4:ℝ) ≠ 0),and_self]

theorem right_logs {u : ℝ} (hu : 1≤u) :
    log (rightArg u-2/3)=log u-log (u+3)+log (4/3) ∧
    log (rightArg u-2)=log 4-log (u+3) ∧
    log (rightArg u)=log (u+1)-log (u+3)+log 2 ∧
    log (rightArg u+1)=log (3*u+5)-log (u+3) ∧
    log (rightArg u+4-radical)=log (rightMinus u)-log (u+3) ∧
    log (rightArg u+4+radical)=log (rightPlus u)-log (u+3) := by
  have hu0 : u ≠ 0 := by linarith
  have hu1 : u+1 ≠ 0 := by linarith
  have hu3 : u+3 ≠ 0 := by linarith
  have hu5 : 3*u+5 ≠ 0 := by linarith
  have hh := affine_positive hu
  have h0 : rightArg u-2/3=((4:ℝ)/3)*u/(u+3) := by unfold rightArg; field_simp; ring
  have h2 : rightArg u-2= -(4/(u+3)) := by unfold rightArg; field_simp; ring
  have h1 : rightArg u+1=(3*u+5)/(u+3) := by unfold rightArg; field_simp; ring
  have hm : rightArg u+4-radical=rightMinus u/(u+3) := by unfold rightArg rightMinus; field_simp; ring
  have hp : rightArg u+4+radical=rightPlus u/(u+3) := by unfold rightArg rightPlus; field_simp; ring
  rw [h0,h2,h1,hm,hp]
  rw [log_div (mul_ne_zero (by norm_num : (4:ℝ)/3 ≠ 0) hu0) hu3,
    log_mul (by norm_num : (4:ℝ)/3 ≠ 0) hu0,log_neg_eq_log,
    log_div (by norm_num : (4:ℝ) ≠ 0) hu3,
    log_div hu5 hu3,log_div hh.2.2.1.ne' hu3,log_div hh.2.2.2.ne' hu3]
  unfold rightArg
  rw [log_div (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hu1) hu3,
    log_mul (by norm_num : (2:ℝ) ≠ 0) hu1]
  constructor
  · ring
  constructor
  · rfl
  constructor
  · ring
  exact ⟨rfl,rfl,rfl⟩

/-- Common logs collected before any signed inequality is spent. -/
theorem fullPrimitive_collected {u : ℝ} (hu : 1≤u) :
    fullPrimitive u=rationalFull u+affineLogs u+constantLog := by
  have hb := argument_bounds hu
  obtain ⟨l0,l1,l2,l3,l4⟩ := left_logs hu
  obtain ⟨r0,r1,r2,r3,r4,r5⟩ := right_logs hu
  unfold fullPrimitive
  rw [primitive_expansion hb.1,primitive_expansion hb.2.2.1,primitive_expansion hb.2.2.1]
  rw [l0,l1,l2,l3,l4,r0,r1,r2,r3,r4,r5]
  unfold rationalFull affineLogs constantLog coeffU coeffThree coeffOne coeffSeven coeffFive
  ring

/-- Exact endpoint formula, retaining all principal-part and quadratic terms. -/
theorem cellMass_collected {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    cellMass a b=rationalFull b-rationalFull a+affineLogs b-affineLogs a := by
  unfold cellMass
  rw [fullPrimitive_collected (ha.trans hab),fullPrimitive_collected ha]
  ring
end TerminalESigned
