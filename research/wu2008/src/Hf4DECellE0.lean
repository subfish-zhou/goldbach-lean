import Hf4DETermsE0
noncomputable section
namespace Hf4DE
open Real

theorem e_cell_0_bounds : (4388277/25000000 : ℝ) ≤ TerminalE.cellMass (1/1 : ℝ) (11/5 : ℝ) ∧ TerminalE.cellMass (1/1 : ℝ) (11/5 : ℝ) ≤ (17553109/100000000 : ℝ) := by
  have h0 := hf4determse0_term_0
  have h1 := hf4determse0_term_1
  have h2 := hf4determse0_term_2
  have h3 := hf4determse0_term_3
  have h4 := hf4determse0_term_4
  have h5 := hf4determse0_term_5
  have h6 := hf4determse0_term_6
  have h7 := hf4determse0_term_7
  have h8 := hf4determse0_term_8
  have hrat : TerminalESigned.rationalFull (11/5 : ℝ)-TerminalESigned.rationalFull (1/1 : ℝ) = (-203440083061975493/15004724598552780000 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (1/1 : ℝ)) (by norm_num : (1/1 : ℝ) ≤ (11/5 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
