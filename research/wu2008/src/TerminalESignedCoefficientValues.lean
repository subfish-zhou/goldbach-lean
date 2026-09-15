import TerminalESignedNine
noncomputable section
namespace TerminalESigned
open Real TerminalE

theorem coefficient_0 : coeffU = (-58040997252859/83735415225000 : ℝ) := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]

theorem coefficient_1 : coeffThree = (-712/945 : ℝ) := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]
  field_simp [radical_pos.ne']
  nlinarith only [radical_sq]

theorem coefficient_2 : coeffOne = (-19/35 : ℝ) := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]

theorem coefficient_3 : coeffSeven = (1409536/2268945 : ℝ) := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]

theorem coefficient_4 : coeffFive = (3913216/15946875 : ℝ) := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]

theorem coefficient_5 : minusCoeff (3/4) = (47000/22869 : ℝ) + (-1400/9801 : ℝ)*radical := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]
  field_simp [radical_pos.ne']
  nlinarith only [radical_sq]

theorem coefficient_6 : plusCoeff (3/4) = (47000/22869 : ℝ) + (1400/9801 : ℝ)*radical := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]
  field_simp [radical_pos.ne']
  nlinarith only [radical_sq]

theorem coefficient_7 : minusCoeff (2/3)-minusCoeff 2 = (169000/242109 : ℝ) + (21400/242109 : ℝ)*radical := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]
  field_simp [radical_pos.ne']
  nlinarith only [radical_sq]

theorem coefficient_8 : plusCoeff (2/3)-plusCoeff 2 = (169000/242109 : ℝ) + (-21400/242109 : ℝ)*radical := by
  norm_num [coeffU,coeffThree,coeffOne,coeffSeven,coeffFive,minusCoeff,plusCoeff,
    mainCoeff,zeroOne,negOne,quadOne,quadZero,TerminalE.residue,q,k,a,b,c,d,TerminalE.e,f,g,h]
  field_simp [radical_pos.ne']
  nlinarith only [radical_sq]

end TerminalESigned
