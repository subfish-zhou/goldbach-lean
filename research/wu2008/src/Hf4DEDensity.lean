import Hf4DETermsD
noncomputable section
namespace Hf4DE
open Real

theorem fullMass_bounds : (858467/5000000 : ℝ) ≤ D0FullDensity.fullMass ∧ D0FullDensity.fullMass ≤ (17169341/100000000 : ℝ) := by
  have h0 := hf4determsd_term_0
  have h1 := hf4determsd_term_1
  have h2 := hf4determsd_term_2
  have h3 := hf4determsd_term_3
  have h4 := hf4determsd_term_4
  have h5 := hf4determsd_term_5
  have h6 := hf4determsd_term_6
  have h7 := hf4determsd_term_7
  have h8 := hf4determsd_term_8
  have hrat : D0FullDensity.rationalFull (5/1 : ℝ)-D0FullDensity.rationalFull (3/1 : ℝ) = (1280091816173/15531252660000 : ℝ) := by
    norm_num [D0FullDensity.rationalFull,D0FullDensity.leftArg,D0FullDensity.rightArg,D0FullDensity.zeroRational,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [D0FullDensity.fullMass_collected]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [D0FullDensity.affineLogs, d_coefficient_0,d_coefficient_1,d_coefficient_2,d_coefficient_3,d_coefficient_4,d_coefficient_5,d_coefficient_6,d_coefficient_7,d_coefficient_8] at *
  norm_num [D0FullDensity.leftMinus,D0FullDensity.leftPlus,D0FullDensity.rightMinus,D0FullDensity.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
