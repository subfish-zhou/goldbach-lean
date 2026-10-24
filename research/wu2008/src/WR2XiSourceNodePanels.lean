import WR2SourceTailPanels
import WR2XiSourceSigmaRational

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Real NodeExtension Finset
open scoped Classical

def nodeLower (S : ℝ) : ℝ :=
  (1105570288/1000000000000)*SourceLogRational.lower (4/(S-1))+
    ∑ k : Fin 9, RationalCandidate.lowerH k*SourceTailPanels.panels S k

theorem nodeLower_le_profile {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) :
    nodeLower S ≤ eProfile (nineProfile RationalCandidate.lowerH) S := by
  have hx : (1:ℝ) ≤ 4/(S-1) := (one_le_div (by linarith)).mpr (by linarith)
  have hs0 : (0:ℝ) ≤ 1105570288/1000000000000 := by norm_num
  have hsig := mul_le_mul sigma_moment_lower (SourceLogRational.lower_le_log hx)
    (SourceLogRational.lower_nonneg hx) (hs0.trans sigma_moment_lower)
  have htail :
      (∑ k : Fin 9, RationalCandidate.lowerH k*SourceTailPanels.panels S k) ≤
        logMoment RationalCandidate.lowerH S := by
    rw [logMoment_expansion _ hS hS5]
    exact sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (SourceTailPanels.panels_le_logMoment hS hS5 k) (RationalCandidate.lowerH_nonneg k))
  exact add_le_add hsig htail

theorem nodeLower_le_extended {i : ℕ} (hi : 11 ≤ i) (hi29 : i ≤ 29) :
    nodeLower (rNode i) ≤ extendedNode RationalCandidate.lowerH i := by
  rw [extendedNode, dif_neg (by omega)]
  apply nodeLower_le_profile
  · dsimp [rNode]
    have h : (11:ℝ) ≤ i := by exact_mod_cast hi
    linarith
  · exact (rNode_bounds hi29).2

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.nodeLower_le_extended
