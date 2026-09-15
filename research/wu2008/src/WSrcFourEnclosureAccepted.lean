import WSrcFourEnclosureRoot
import WSrcBuchstabLowerRoot

noncomputable section
namespace WuTarget.SourceFourAccepted
open Wu2008DoubleSieve Wu08OriginalFourWeights

/-- Both bounds concern the unchanged compiled original integral pair. -/
theorem original_pair_enclosure :
    (16959/25000 : ℝ) < original10+original11 ∧
      original10+original11 < (851/1250 : ℝ) :=
  WuSource.SrcFourEnclosure.original_pair_conditional_enclosure
    WuSource.SrcBuchstabLower.buchstab_lower56

/-- The printed pair cannot be an upper bound for this literal integral pair. -/
theorem printed_pair_gap :
    (30197/1000000 : ℝ) < original10+original11-
      WuSource.SrcFourEnclosure.printedPair ∧
    original10+original11-WuSource.SrcFourEnclosure.printedPair <
      (32637/1000000 : ℝ) :=
  WuSource.SrcFourEnclosure.printed_gap_conditional
    WuSource.SrcBuchstabLower.buchstab_lower56

theorem old_budget_impossible : ¬ original10+original11 ≤ (13/20 : ℝ) := by
  linarith only [original_pair_enclosure.1]

end WuTarget.SourceFourAccepted

set_option pp.fullNames true
set_option pp.explicit true
#check @WuTarget.SourceFourAccepted.original_pair_enclosure
#check @WuTarget.SourceFourAccepted.printed_pair_gap
#check @WuTarget.SourceFourAccepted.old_budget_impossible
#check @WuSource.SrcFourEnclosure.actual_pair_upper
#check @WuSource.SrcFourEnclosure.ordinary_P2_enclosed
#print axioms WuTarget.SourceFourAccepted.original_pair_enclosure
#print axioms WuTarget.SourceFourAccepted.printed_pair_gap
#print axioms WuTarget.SourceFourAccepted.old_budget_impossible
#print axioms WuSource.SrcFourEnclosure.actual_pair_upper
#print axioms WuSource.SrcFourEnclosure.ordinary_P2_enclosed
