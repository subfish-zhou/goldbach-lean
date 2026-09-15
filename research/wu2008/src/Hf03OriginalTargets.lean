import Hf03Assembly0
import Hf03Assembly3
namespace Hf03OriginalTargets
open Real Wu2008DoubleSieve ActualNineFeedback
noncomputable section

/-- The four nonterminal original rows, reusing the existing certificates for rows one and two. -/
theorem original_hf_first_four (i : Fin 5) (hi : i.val < 4) :
    NineFeedbackStrength.originalH (Fin.natAdd 4 i) ≤
      Wu04FirstCore.publication i+
        firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) := by
  rcases i with ⟨i,hi5⟩
  change i < 4 at hi
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact Hf03Scalar.original_hf_0
  · exact SigmaJFirstCertificates.original_hf_1
  · exact SigmaJFirstCertificates.original_hf_2
  · exact Hf03Scalar.original_hf_3

end
end Hf03OriginalTargets
