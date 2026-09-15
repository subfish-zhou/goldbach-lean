import SigmaCorrectionFullFTC
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength
noncomputable section

def poleFourPaid (p c1 c2 c3 c4 a b : ℝ) : ℝ :=
  SigmaRemaining.polePaid p c1 c2 c3 a b-c4/3*(1/(b+p)^3-1/(a+p)^3)

theorem poleFourPaid_le (p c1 c2 c3 c4 : ℝ) {a b : ℝ}
    (ha : 0<a+p) (hab : a≤b) :
    poleFourPaid p c1 c2 c3 c4 a b ≤
      poleFourPrimitive p c1 c2 c3 c4 b-poleFourPrimitive p c1 c2 c3 c4 a := by
  have h := SigmaRemaining.polePaid_le p c1 c2 c3 ha hab
  unfold poleFourPaid poleFourPrimitive
  simp only [div_eq_mul_inv,mul_inv_rev]
  linarith only [h]

def minusA (t : ℝ) : ℝ := (t+2)/3+4-TerminalE.radical
def plusA (t : ℝ) : ℝ := (t+2)/3+4+TerminalE.radical
def minusB (t : ℝ) : ℝ := t+9-F1JointFTC.root
def plusB (t : ℝ) : ℝ := t+9+F1JointFTC.root

theorem rootsA_pos {t : ℝ} (ht : 1≤t) : 0 < minusA t ∧ 0<plusA t := by
  unfold minusA plusA
  constructor <;> linarith only [ht,TerminalE.radical_pos,TerminalE.radical_lt_four]

theorem rootsB_pos {t : ℝ} (ht : 1≤t) : 0 < minusB t ∧ 0<plusB t := by
  unfold minusB plusB
  constructor <;> linarith only [ht,F1JointFTC.root_pos,F1JointFTC.root_lt_eight]

def coeffAMinus (f g : ℝ) : ℝ := f/2+(g-14*f)/(6*TerminalE.radical)
def coeffAPlus (f g : ℝ) : ℝ := f/2-(g-14*f)/(6*TerminalE.radical)
def coeffBMinus (f g : ℝ) : ℝ := f/2+(g-9*f)/(2*F1JointFTC.root)
def coeffBPlus (f g : ℝ) : ℝ := f/2-(g-9*f)/(2*F1JointFTC.root)

theorem quadraticA_collected (f g : ℝ) {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    quadraticAPrimitive f g b-quadraticAPrimitive f g a =
      coeffAMinus f g*log (minusA b/minusA a)+
      coeffAPlus f g*log (plusA b/plusA a) := by
  obtain ⟨ham,hap⟩ := rootsA_pos ha
  obtain ⟨hbm,hbp⟩ := rootsA_pos (ha.trans hab)
  have he (t : ℝ) : TerminalE.q ((t+2)/3)=minusA t*plusA t := by
    unfold TerminalE.q minusA plusA
    nlinarith only [TerminalE.radical_sq]
  unfold quadraticAPrimitive TerminalE.quadraticPrimitive
  rw [he a,he b,log_mul ham.ne' hap.ne',log_mul hbm.ne' hbp.ne',
    log_div hbm.ne' ham.ne',log_div hbp.ne' hap.ne']
  unfold coeffAMinus coeffAPlus minusA plusA
  ring

theorem quadraticB_collected (f g : ℝ) {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    SigmaInnerPaid.quadraticPrimitive f g b-SigmaInnerPaid.quadraticPrimitive f g a =
      coeffBMinus f g*log (minusB b/minusB a)+
      coeffBPlus f g*log (plusB b/plusB a) := by
  obtain ⟨ham,hap⟩ := rootsB_pos ha
  obtain ⟨hbm,hbp⟩ := rootsB_pos (ha.trans hab)
  have he (t : ℝ) : (t+1)^2+16*(t+1)+4=minusB t*plusB t := by
    unfold minusB plusB
    nlinarith only [F1JointFTC.root_sq]
  have ht (t : ℝ) : t+1+8=t+9 := by ring
  unfold SigmaInnerPaid.quadraticPrimitive F1JointFTC.quadraticPrimitive
  rw [he a,he b,log_mul ham.ne' hap.ne',log_mul hbm.ne' hbp.ne',ht a,ht b,
    log_div hbm.ne' ham.ne',log_div hbp.ne' hap.ne']
  unfold coeffBMinus coeffBPlus minusB plusB
  ring

def quadraticAPaid (f g a b : ℝ) : ℝ :=
  RemainingHf.signed (coeffAMinus f g) (minusA b/minusA a)+
  RemainingHf.signed (coeffAPlus f g) (plusA b/plusA a)

def quadraticBPaid (f g a b : ℝ) : ℝ :=
  RemainingHf.signed (coeffBMinus f g) (minusB b/minusB a)+
  RemainingHf.signed (coeffBPlus f g) (plusB b/plusB a)

theorem quadraticAPaid_le (f g : ℝ) {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    quadraticAPaid f g a b ≤ quadraticAPrimitive f g b-quadraticAPrimitive f g a := by
  rw [quadraticA_collected f g ha hab]
  apply add_le_add
  · apply RemainingHf.signed_le
    apply (one_le_div (rootsA_pos ha).1).mpr
    unfold minusA
    linarith only [hab]
  · apply RemainingHf.signed_le
    apply (one_le_div (rootsA_pos ha).2).mpr
    unfold plusA
    linarith only [hab]

theorem quadraticBPaid_le (f g : ℝ) {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    quadraticBPaid f g a b ≤
      SigmaInnerPaid.quadraticPrimitive f g b-SigmaInnerPaid.quadraticPrimitive f g a := by
  rw [quadraticB_collected f g ha hab]
  apply add_le_add
  · apply RemainingHf.signed_le
    apply (one_le_div (rootsB_pos ha).1).mpr
    unfold minusB
    linarith only [hab]
  · apply RemainingHf.signed_le
    apply (one_le_div (rootsB_pos ha).2).mpr
    unfold plusB
    linarith only [hab]

end
end SigmaCorrectionFTC
