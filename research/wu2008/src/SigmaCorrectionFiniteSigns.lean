import SigmaCorrectionNineProfile
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength RemainingHf
noncomputable section

theorem quadratic_coefficient_signs :
    0 < coeffAMinus (-7903489340/2035338627) (6526017140/2035338627) ∧
    coeffAPlus (-7903489340/2035338627) (6526017140/2035338627)<0 ∧
    coeffBMinus fullQBOne fullQBZero<0 ∧ 0 < coeffBPlus fullQBOne fullQBZero := by
  have hdA : 0<6*TerminalE.radical := mul_pos (by norm_num) TerminalE.radical_pos
  have hdB : 0<2*F1JointFTC.root := mul_pos (by norm_num) F1JointFTC.root_pos
  have ha (f g : ℝ) : coeffAMinus f g=(3*f*TerminalE.radical+g-14*f)/(6*TerminalE.radical) := by
    unfold coeffAMinus
    field_simp [TerminalE.radical_pos.ne',F1JointFTC.root_pos.ne']
    ring
  have hb (f g : ℝ) : coeffAPlus f g=(3*f*TerminalE.radical-g+14*f)/(6*TerminalE.radical) := by
    unfold coeffAPlus
    field_simp [TerminalE.radical_pos.ne',F1JointFTC.root_pos.ne']
    ring
  have hc (f g : ℝ) : coeffBMinus f g=(f*F1JointFTC.root+g-9*f)/(2*F1JointFTC.root) := by
    unfold coeffBMinus
    field_simp [TerminalE.radical_pos.ne',F1JointFTC.root_pos.ne']
    ring
  have hd (f g : ℝ) : coeffBPlus f g=(f*F1JointFTC.root-g+9*f)/(2*F1JointFTC.root) := by
    unfold coeffBPlus
    field_simp [TerminalE.radical_pos.ne',F1JointFTC.root_pos.ne']
    ring
  rw [ha,hb,hc,hd]
  refine ⟨div_pos ?_ hdA,div_neg_of_neg_of_pos ?_ hdA,div_neg_of_neg_of_pos ?_ hdB,div_pos ?_ hdB⟩
  · nlinarith only [TerminalE.radical_lt_four]
  · nlinarith only [TerminalE.radical_pos]
  · unfold fullQBOne fullQBZero
    nlinarith only [F1JointFTC.root_lt_eight]
  · unfold fullQBOne fullQBZero
    nlinarith only [F1JointFTC.root_pos]

/-- Exactly the same full cell ledger, now with all signs decided in Lean. -/
def fullCellFinite (a b : ℝ) : ℝ :=
  poleFourPaid 0 (23459573759494777727/159040724270459062500) (-7668814423/91965608043750)
    (2914132/179480109375) (-44/28021875) a b+
  poleFourPaid 1 (-4/35) 0 0 0 a b+
  poleFourPaid 2 (-3/20) 0 0 0 a b+
  poleFourPaid 3 (-36416/76545) (-2432/25515) (512/1701) (1024/2835) a b+
  poleFourPaid 5 (26940087976/24020390625) (37444664/145578125) (-41190048/13234375) (-1134432/240625) a b+
  poleFourPaid (5/3) (-37120077824/45581484375) (759382016/3906984375)
    (-276955136/1674421875) (4456448/143521875) a b+
  (coeffAMinus (-7903489340/2035338627) (6526017140/2035338627)*splitLower (minusA b/minusA a)+
    coeffAPlus (-7903489340/2035338627) (6526017140/2035338627)*splitUpper (plusA b/plusA a))+
  (fullRational b-fullRational a)+
  (coeffBMinus fullQBOne fullQBZero*splitUpper (minusB b/minusB a)+
    coeffBPlus fullQBOne fullQBZero*splitLower (plusB b/plusB a))

theorem fullCellPaid_eq_finite (a b : ℝ) : fullCellPaid a b=fullCellFinite a b := by
  obtain ⟨hAm,hAp,hBm,hBp⟩ := quadratic_coefficient_signs
  simp only [fullCellPaid,fullCellFinite,quadraticAPaid,quadraticBPaid,signed,
    if_pos hAm.le,if_neg (not_le.mpr hAp),if_neg (not_le.mpr hBm),if_pos hBp.le]

/-- Original numerator plus retained complete FTC correction; nothing is silently paid twice. -/
def fullUnpaid (a b : ℝ) : ℝ := fullPrimitive b-fullPrimitive a-fullCellPaid a b

theorem fullUnpaid_nonneg {a b : ℝ} (ha : 1≤a) (hab : a≤b) : 0≤fullUnpaid a b :=
  sub_nonneg.mpr (fullCellPaid_le ha hab)

theorem exact_full_payment_remainder {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    SigmaPrimitiveCells.cellMass a b+SigmaSignedCells.correctionMass a b=
      fullCellPaid a b+fullUnpaid a b := by
  rw [← fullCell_identity ha hab]
  unfold fullUnpaid
  ring

end
end SigmaCorrectionFTC
