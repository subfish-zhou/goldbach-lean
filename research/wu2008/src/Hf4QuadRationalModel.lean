import Hf4QuadRationalModelCore
import Hf4QuadModelRadical

namespace Hf4Quad.RationalModel
theorem radical :
    (⟨7745966692415/2000000000000,0,0,0,1/2000000000000⟩ : Certificate).Valid
      (fun _ => TerminalE.radical) := by
  simpa [Certificate.Valid, Certificate.cubic] using Model.radical

end Hf4Quad.RationalModel
