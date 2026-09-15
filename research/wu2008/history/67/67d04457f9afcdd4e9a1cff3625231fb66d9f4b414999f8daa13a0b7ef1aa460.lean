import E05SixthMajorPayment

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SharpMassBalance
open scoped Interval

namespace WuTarget.E05SixthMajor

def netOrdinaryCredit : ℝ := newCredit/4
def displayCredit : ℝ := ((381/100)-E05Sixth.sixthLower)/4
def fullCoefficient : ℝ := E05Sixth.coefficientWithSixth majorLower
def displayedCoefficient : ℝ := E05Sixth.coefficientWithSixth (381/100)

theorem strict_target_arithmetic :
    (381/100:ℝ) < 3783117/1000000+newCredit := by
  norm_num [newCredit,innerCredit,innerRate,innerDenom1,innerDenom2,
    fifthExtraCredit,seventhCredit,outerCredit,E05Sixth.denominatorCap,
    E05Sixth.fifthLogTerm,z0,Phase25.kx,a,b,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem majorLower_above_target : (381/100:ℝ) < majorLower := by
  unfold majorLower
  linarith only [strict_target_arithmetic,E05Sixth.sixthLower_bounds.1]

theorem newCredit_positive : 0 < newCredit := by
  linarith only [strict_target_arithmetic]

theorem netOrdinaryCredit_lower : (26883/4000000:ℝ) < netOrdinaryCredit := by
  unfold netOrdinaryCredit
  linarith only [strict_target_arithmetic]

theorem displayCredit_bounds :
    (13441/2000000:ℝ) < displayCredit ∧ displayCredit ≤ 26883/4000000 := by
  unfold displayCredit
  constructor <;> linarith only [E05Sixth.sixthLower_bounds.1,E05Sixth.sixthLower_bounds.2]

theorem displayCredit_exact : displayCredit =
    ((381/100:ℝ)-
      4791546038685779108598859719736646859698318702491580044634838565576580259629410262543761209306626076510312714948495836722766345438906967946254533251334982810497884808610993147634418286473375077/
      1266560227577067117922148411782929509583092926655824581729130538458223093026069800921359527583029777923355459074352756831259200270049778587584252271822884241375819569566884910171288622435944000)/4 := by
  unfold displayCredit
  rw [E05Sixth.sixthLower_exact]

theorem correction_no_double_payment (x : ℝ) :
    densityInner x-E05Sixth.correctionInner x =
      (2/21)*(lam-x-b)^7/E05Sixth.denominatorCap+
        (1/28)*(lam-x-b)^8/(E05Sixth.denominatorCap*z0^2) := by
  unfold densityInner
  ring

theorem first_round_net_identity : majorLower-E05Sixth.sixthLower =
    innerCredit+fifthExtraCredit+seventhCredit+outerCredit := by
  unfold majorLower newCredit
  ring

theorem actual_remaining_identity :
    (Wu08TerminalAlignment.sixthMain-E05Sixth.sixthLower)/4 =
      netOrdinaryCredit+(Wu08TerminalAlignment.sixthMain-majorLower)/4 := by
  unfold netOrdinaryCredit majorLower
  ring

theorem actual_remaining_nonnegative :
    0 ≤ Wu08TerminalAlignment.sixthMain-majorLower :=
  sub_nonneg.mpr majorLower_le_actual

theorem fullCoefficient_le_actual : fullCoefficient ≤ PositiveTwoPayment.Qtwo := by
  rw [← E05Sixth.full_terminal_identity]
  unfold fullCoefficient E05Sixth.coefficientWithSixth
  linarith only [majorLower_le_actual]

theorem full_signed_net_identity :
    fullCoefficient-E05Sixth.coefficientWithSixth E05Sixth.sixthLower =
      netOrdinaryCredit := by
  unfold fullCoefficient E05Sixth.coefficientWithSixth majorLower netOrdinaryCredit
  ring

theorem displayed_signed_net_identity :
    displayedCoefficient-E05Sixth.coefficientWithSixth E05Sixth.sixthLower =
      displayCredit := by
  unfold displayedCoefficient E05Sixth.coefficientWithSixth displayCredit
  ring

theorem displayed_slack_identity :
    fullCoefficient-displayedCoefficient = (majorLower-381/100)/4 := by
  unfold fullCoefficient displayedCoefficient E05Sixth.coefficientWithSixth
  ring

theorem ordinary_P2_full (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (fullCoefficient-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hd,T,hT,hcount⟩ := PositiveTwoPayment.ordinary_P2 η hη
  refine ⟨δ,hδ,hd,T,hT,fun N hN he => ?_⟩
  have hm := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right fullCoefficient_le_actual η) hm).trans
    (hcount N hN he)

theorem ordinary_P2_display :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        displayedCoefficient*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hη : 0 < (majorLower-381/100)/8 := by linarith only [majorLower_above_target]
  obtain ⟨δ,hδ,hd,T,hT,hcount⟩ := ordinary_P2_full _ hη
  refine ⟨δ,hδ,hd,T,hT,fun N hN he => ?_⟩
  have hm := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  have hcoef : displayedCoefficient ≤ fullCoefficient-(majorLower-381/100)/8 := by
    linarith only [displayed_slack_identity,hη]
  exact (mul_le_mul_of_nonneg_right hcoef hm).trans (hcount N hN he)

theorem original_domain_preserved : Wu08TerminalAlignment.sixthMain =
    4*∫ x in a..b, ∫ y in b..(lam-x), truncatedSixthZeroDeltaRegular 0 (x,y) :=
  ClassicalLossBottleneck.sixth_actual_domain

theorem recurrence_not_spent :
    0 ≤ Wu08TerminalAlignment.sixthMain-ClassicalLossBottleneck.sixthLogIntegral ∧
    Wu08TerminalAlignment.sixthMain-ClassicalLossBottleneck.sixthLogIntegral < (1/100000:ℝ) :=
  E05Sixth.recurrence_unspent

end WuTarget.E05SixthMajor
