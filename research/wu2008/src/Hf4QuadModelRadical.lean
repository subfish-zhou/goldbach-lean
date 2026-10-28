import Hf4QuadModelBasic
import Hf4RadicalBounds

noncomputable section
namespace Hf4Quad
theorem Model.radical : Model (fun _ => TerminalE.radical)
    ⟨(7745966692415/2000000000000),0,0,0⟩ (1/2000000000000) := by
  intro x _
  simp only [Cubic.eval,zero_mul,add_zero]
  apply abs_le.mpr
  constructor <;> linarith only [Hf4Target.radical_bounds.1,Hf4Target.radical_bounds.2]

end Hf4Quad
