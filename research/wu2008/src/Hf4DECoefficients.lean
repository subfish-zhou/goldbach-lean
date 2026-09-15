import Hf4DEBase
noncomputable section
namespace Hf4DE
open Real

theorem d_coefficient_0 : D0FullDensity.coeffV = ((505552216415/131406371712 : ℝ)+(0/1 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]

theorem d_coefficient_1 : D0FullDensity.coeffMinusOne = ((0/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  field_simp [TerminalE.radical_pos.ne']
  nlinarith only [TerminalE.radical_sq]

theorem d_coefficient_2 : D0FullDensity.coeffPlusThree = ((1424/945 : ℝ)+(0/1 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  field_simp [TerminalE.radical_pos.ne']
  nlinarith only [TerminalE.radical_sq]

theorem d_coefficient_3 : D0FullDensity.coeffTriple = ((-72704/25515 : ℝ)+(0/1 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]

theorem d_coefficient_4 : D0FullDensity.coeffEleven = ((-4830208/13835745 : ℝ)+(0/1 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]

theorem d_coefficient_5 : (TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2)) = ((-4400/3969 : ℝ)+(-2000/3969 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  field_simp [TerminalE.radical_pos.ne']
  nlinarith only [TerminalE.radical_sq]

theorem d_coefficient_6 : (TerminalESigned.plusCoeff (-3/2)-TerminalESigned.plusCoeff (1/2)) = ((-4400/3969 : ℝ)+(2000/3969 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  field_simp [TerminalE.radical_pos.ne']
  nlinarith only [TerminalE.radical_sq]

theorem d_coefficient_7 : (TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus) = ((-7600/1431 : ℝ)+(-35600/30051 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  field_simp [TerminalE.radical_pos.ne']
  nlinarith only [TerminalE.radical_sq]

theorem d_coefficient_8 : (TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus) = ((-7600/1431 : ℝ)+(35600/30051 : ℝ)*TerminalE.radical) := by
  norm_num [D0FullDensity.coeffV,D0FullDensity.coeffMinusOne,D0FullDensity.coeffPlusThree,D0FullDensity.coeffTriple,D0FullDensity.coeffEleven,D0FullDensity.zeroMain,D0FullDensity.zeroNeg,D0FullDensity.zeroMinus,D0FullDensity.zeroPlus,TerminalESigned.minusCoeff,TerminalESigned.plusCoeff,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  field_simp [TerminalE.radical_pos.ne']
  nlinarith only [TerminalE.radical_sq]

theorem payment_exact : Hf4Outer.payment = (13054776369978811079456756068459606337936360085350614226411067305280799821148874985779/358648396284436909774909909136792580513300834454414085598313552305364670054400000000000000000000 : ℝ) := by
  norm_num [Hf4Outer.payment, Fin.sum_univ_succ, NineFeedbackStrength.originalH, Hf4Outer.cellPayment, NodeExtension.upperLeft, NodeExtension.upperNode]

end Hf4DE
