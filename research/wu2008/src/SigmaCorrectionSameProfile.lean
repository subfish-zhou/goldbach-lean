import SigmaCorrectionFiniteSigns
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength NodeExtension FirstFeedbackIntegrals SigmaSignedCells
open scoped BigOperators
noncomputable section

/-- Same correction alone, with repeated and simple quadratic log coefficients collected. -/
def correctionCollectedPrimitive (t : ℝ) : ℝ :=
  (-22/189)*t+
  poleFourPrimitive (0) (148297720234751447/159040724270459062500) (-451289133137/1379484120656250) (51645526/538440328125) (-1352/84065625) t+
  poleFourPrimitive (1) (-4/35) (0) (0) (0) t+
  poleFourPrimitive (2) (-3/20) (0) (0) (0) t+
  poleFourPrimitive (3) (83248/76545) (-7136/3645) (3968/1701) (1024/2835) t+
  poleFourPrimitive (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) t+
  poleFourPrimitive (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) t+
  quadraticAPrimitive (-7903489340/2035338627) (6526017140/2035338627) t+fullRational t+
  SigmaInnerPaid.quadraticPrimitive (235662707120/19931774247) (420448769080/19931774247) t

theorem correctionCollected_identity (t : ℝ) : correctionCollectedPrimitive t=primitive t := by
  unfold correctionCollectedPrimitive primitive repeatedPrimitive fullRational hermiteA hermiteB
    SigmaInnerPaid.quadraticPrimitive F1JointFTC.quadraticPrimitive
  ring

def correctionCellPaid (a b : ℝ) : ℝ :=
  (-22/189)*(b-a)+
  poleFourPaid (0) (148297720234751447/159040724270459062500) (-451289133137/1379484120656250) (51645526/538440328125) (-1352/84065625) a b+
  poleFourPaid (1) (-4/35) (0) (0) (0) a b+
  poleFourPaid (2) (-3/20) (0) (0) (0) a b+
  poleFourPaid (3) (83248/76545) (-7136/3645) (3968/1701) (1024/2835) a b+
  poleFourPaid (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) a b+
  poleFourPaid (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) a b+
  quadraticAPaid (-7903489340/2035338627) (6526017140/2035338627) a b+(fullRational b-fullRational a)+
  quadraticBPaid (235662707120/19931774247) (420448769080/19931774247) a b

theorem correctionCellPaid_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    correctionCellPaid a b≤correctionMass a b := by
  rw [correctionMass_ftc ha hab,← correctionCollected_identity a,← correctionCollected_identity b]
  have h0 := poleFourPaid_le (0) (148297720234751447/159040724270459062500) (-451289133137/1379484120656250) (51645526/538440328125) (-1352/84065625) (by linarith : 0<a+0) hab
  have h1 := poleFourPaid_le (1) (-4/35) (0) (0) (0) (by linarith : 0<a+1) hab
  have h2 := poleFourPaid_le (2) (-3/20) (0) (0) (0) (by linarith : 0<a+2) hab
  have h3 := poleFourPaid_le (3) (83248/76545) (-7136/3645) (3968/1701) (1024/2835) (by linarith : 0<a+3) hab
  have h4 := poleFourPaid_le (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) (by linarith : 0<a+5) hab
  have h5 := poleFourPaid_le (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) (by linarith : 0<a+5/3) hab
  have hA := quadraticAPaid_le (-7903489340/2035338627) (6526017140/2035338627) ha hab
  have hB := quadraticBPaid_le (235662707120/19931774247) (420448769080/19931774247) ha hab
  unfold correctionCellPaid correctionCollectedPrimitive
  linarith only [h0,h1,h2,h3,h4,h5,hA,hB]

def correctionNumeratorPaid : ℝ := ∑ k : Fin 9,NineFeedbackStrength.originalH k*
  correctionCellPaid (upperLeft k) (upperNode k)

theorem correctionNumeratorPaid_le : correctionNumeratorPaid≤correctionNumerator := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left
    (correctionCellPaid_le (original_cell_bounds k).1 (original_cell_bounds k).2.1)
    (CoupledIntegralRecovery.originalH_nonneg k)

/-- Literal finite payment back into the original correctedProfile, not a replacement premise. -/
def paidCorrectedProfile : ℝ := max SigmaSignedCells.profileLower
  (SigmaSignedCells.finiteLower+correctionNumeratorPaid/(1-SigmaRemaining.d0Paid))

theorem paidCorrectedProfile_le : paidCorrectedProfile≤correctedProfile := by
  apply max_le SigmaSignedCells.profileLower_le_corrected
  apply le_trans _ (le_max_right _ _)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right correctionNumeratorPaid_le
    (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le)

def paidCorrectedCoupled (p : Wu2008DoubleSieve.SecondFunctionalParameters) : ℝ :=
  SigmaSignedCells.coupledLower p+CoupledFiniteAssembly.aCoefficient p*
    (paidCorrectedProfile-SigmaSignedCells.profileLower)

theorem paidCorrectedCoupled_le (i : Fin 4) : paidCorrectedCoupled (ActualNineFeedback.coupledRow i)≤
    ActualNineFeedback.coupledFeedback (ActualNineFeedback.coupledRow i) NineFeedbackStrength.originalH := by
  have h := mul_le_mul_of_nonneg_left paidCorrectedProfile_le
    (CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i))
  have hc := SigmaSignedCells.correctedCoupledLower_le i
  unfold paidCorrectedCoupled SigmaSignedCells.correctedCoupledLower at *
  linarith only [h,hc]

end
end SigmaCorrectionFTC
