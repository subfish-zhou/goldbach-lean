import TerminalESignedCoefficientValues

noncomputable section
namespace TerminalESigned
open Real TerminalE NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped BigOperators

theorem coefficient_signs : coeffU<0 ∧ coeffThree<0 ∧ coeffOne<0 ∧
    0<coeffSeven ∧ 0<coeffFive ∧ 0 < minusCoeff (3/4) ∧ 0<plusCoeff (3/4) ∧
    0 < minusCoeff (2/3)-minusCoeff 2 ∧ 0<plusCoeff (2/3)-plusCoeff 2 := by
  rw [coefficient_0,coefficient_1,coefficient_2,coefficient_3,coefficient_4,
    coefficient_5,coefficient_6,coefficient_7,coefficient_8]
  norm_num only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | trivial | linarith only [radical_pos,radical_lt_four]

/-- Fixed, sign-resolved expression: three upper and six lower atoms, once-split only. -/
def cellFinite (a b : ℝ) : ℝ := rationalFull b-rationalFull a+
  coeffU*RemainingHf.splitUpper (b/a)+coeffThree*RemainingHf.splitUpper ((b+3)/(a+3))+
  coeffOne*RemainingHf.splitUpper ((b+1)/(a+1))+coeffSeven*RemainingHf.splitLower ((b+7)/(a+7))+
  coeffFive*RemainingHf.splitLower ((3*b+5)/(3*a+5))+
  minusCoeff (3/4)*RemainingHf.splitLower (leftMinus b/leftMinus a)+
  plusCoeff (3/4)*RemainingHf.splitLower (leftPlus b/leftPlus a)+
  (minusCoeff (2/3)-minusCoeff 2)*RemainingHf.splitLower (rightMinus b/rightMinus a)+
  (plusCoeff (2/3)-plusCoeff 2)*RemainingHf.splitLower (rightPlus b/rightPlus a)

theorem cellPaid_eq_cellFinite (a b : ℝ) : cellPaid a b=cellFinite a b := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := coefficient_signs
  simp only [cellPaid,cellFinite,logPaid,RemainingHf.signed,
    if_neg (not_le.mpr h0),if_neg (not_le.mpr h1),if_neg (not_le.mpr h2),
    if_pos h3.le,if_pos h4.le,if_pos h5.le,if_pos h6.le,if_pos h7.le,if_pos h8.le]

/-- Literal full E remainder, not the old paidCells difference. -/
def eUnpaid : ℝ := TerminalECells.mass NineFeedbackStrength.originalH-massPaid NineFeedbackStrength.originalH

theorem eUnpaid_nonneg : 0≤eUnpaid :=
  sub_nonneg.mpr (massPaid_le CoupledIntegralRecovery.originalH_nonneg)

/-- The common log-two profile survives once and with its original sign. -/
def profileLogUnpaid : ℝ :=
  (log 2-RemainingHf.splitLower 2)*SigmaRemaining.finiteLower NineFeedbackStrength.originalH

theorem profileLogUnpaid_nonneg : 0≤profileLogUnpaid :=
  mul_nonneg (sub_nonneg.mpr (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2)))
    SigmaRemaining.original_finiteLower_pos.le

theorem exact_terminal_remainders :
    TerminalECells.lower=finiteLower+profileLogUnpaid+eUnpaid := by
  unfold TerminalECells.lower finiteLower profileLogUnpaid eUnpaid
  ring

/-- The accepted parent sigma branch can consume this same E ledger without duplication. -/
def jointFiniteLower : ℝ := RemainingHf.splitLower 2*SigmaPrimitiveCells.profileLower+
  max (RemainingHf.paidCells NineFeedbackStrength.originalH 3) (massPaid NineFeedbackStrength.originalH)

theorem jointFiniteLower_le : jointFiniteLower≤TerminalECells.jointLower := by
  have hlog := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2)) SigmaPrimitiveCells.profileLower_pos.le
  have he := max_le_max_left (RemainingHf.paidCells NineFeedbackStrength.originalH 3)
    (massPaid_le CoupledIntegralRecovery.originalH_nonneg)
  unfold jointFiniteLower TerminalECells.jointLower
  exact add_le_add hlog he

theorem jointFiniteLower_le_actual :
    jointFiniteLower≤firstFeedback NineFeedbackStrength.originalH 3 3 :=
  jointFiniteLower_le.trans TerminalECells.jointLower_le
end TerminalESigned
