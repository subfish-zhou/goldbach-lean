import W10Interval

noncomputable section
namespace WuTarget.W10

theorem coeffA_bounds :
    ((-124079028436551784033 : ℝ) / 100000000000000000) ≤ TailWholeCommonLog.coeffA ∧ TailWholeCommonLog.coeffA ≤ ((-1240790284365517840329 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffA_exact]
  norm_num

theorem coeffAC_bounds :
    ((-220389989765102527713 : ℝ) / 200000000000000000) ≤ TailWholeCommonLog.coeffAC ∧ TailWholeCommonLog.coeffAC ≤ ((-275487487206378159641 : ℝ) / 250000000000000000) := by
  rw [TailWholeCommonLog.coeffAC_exact]
  norm_num

theorem coeffB_bounds :
    ((7635805795815291101 : ℝ) / 500000000000000000) ≤ TailWholeCommonLog.coeffB ∧ TailWholeCommonLog.coeffB ≤ ((15271611591630582203 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffB_exact]
  norm_num

theorem coeffD_bounds :
    ((992731213898699263461 : ℝ) / 500000000000000000) ≤ TailWholeCommonLog.coeffD ∧ TailWholeCommonLog.coeffD ≤ ((1985462427797398526923 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffD_exact]
  norm_num

theorem coeffS_bounds :
    ((-6650189604019169339 : ℝ) / 125000000000000000) ≤ TailWholeCommonLog.coeffS ∧ TailWholeCommonLog.coeffS ≤ ((-53201516832153354711 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffS_exact]
  norm_num

theorem coeffTwo_bounds :
    ((25526114476033728323 : ℝ) / 40000000000000000) ≤ TailWholeCommonLog.coeffTwo ∧ TailWholeCommonLog.coeffTwo ≤ ((159538215475210802019 : ℝ) / 250000000000000000) := by
  rw [TailWholeCommonLog.coeffTwo_exact]
  norm_num

theorem coeffThreeHalf_bounds :
    ((-3360154703556056169 : ℝ) / 1000000000000000000) ≤ TailWholeCommonLog.coeffThreeHalf ∧ TailWholeCommonLog.coeffThreeHalf ≤ ((-420019337944507021 : ℝ) / 125000000000000000) := by
  rw [TailWholeCommonLog.coeffThreeHalf_exact]
  norm_num

theorem poleZero_bounds :
    ((641513016604399264243 : ℝ) / 1000000000000000000) ≤ TailWholeCommonLog.poleZero ∧ TailWholeCommonLog.poleZero ≤ ((160378254151099816061 : ℝ) / 250000000000000000) := by
  rw [TailWholeCommonLog.poleZero_exact]
  norm_num

theorem poleOne_bounds :
    ((-19631766295186638371 : ℝ) / 1000000000000000000) ≤ TailWholeCommonLog.poleOne ∧ TailWholeCommonLog.poleOne ≤ ((-1963176629518663837 : ℝ) / 100000000000000000) := by
  rw [TailWholeCommonLog.poleOne_exact]
  norm_num

theorem coeffAM_bounds :
    ((-163036047834043373289 : ℝ) / 250000000000000000) ≤ TailWholeCommonLog.coeffAM ∧ TailWholeCommonLog.coeffAM ≤ ((-326072095668086746577 : ℝ) / 500000000000000000) := by
  rw [TailWholeCommonLog.coeffAM_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffAP_bounds :
    ((25993938647819149759 : ℝ) / 50000000000000000) ≤ TailWholeCommonLog.coeffAP ∧ TailWholeCommonLog.coeffAP ≤ ((519878772956382995181 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffAP_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffTM_bounds :
    ((20561899025519903801 : ℝ) / 1000000000000000000) ≤ TailWholeCommonLog.coeffTM ∧ TailWholeCommonLog.coeffTM ≤ ((10280949512759951901 : ℝ) / 500000000000000000) := by
  rw [TailWholeCommonLog.coeffTM_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffTP_bounds :
    ((3519797514694061571 : ℝ) / 1000000000000000000) ≤ TailWholeCommonLog.coeffTP ∧ TailWholeCommonLog.coeffTP ≤ ((879949378673515393 : ℝ) / 250000000000000000) := by
  rw [TailWholeCommonLog.coeffTP_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffBM_bounds :
    ((15966112662876295391 : ℝ) / 250000000000000000) ≤ TailWholeCommonLog.coeffBM ∧ TailWholeCommonLog.coeffBM ≤ ((12772890130301036313 : ℝ) / 200000000000000000) := by
  rw [TailWholeCommonLog.coeffBM_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffBP_bounds :
    ((-3559431811358365031 : ℝ) / 62500000000000000) ≤ TailWholeCommonLog.coeffBP ∧ TailWholeCommonLog.coeffBP ≤ ((-11390181796346768099 : ℝ) / 200000000000000000) := by
  rw [TailWholeCommonLog.coeffBP_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffDM_bounds :
    ((12906388719191361 : ℝ) / 31250000000000000) ≤ TailWholeCommonLog.coeffDM ∧ TailWholeCommonLog.coeffDM ≤ ((413004439014123563 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffDM_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem coeffDP_bounds :
    ((-150247645489948235737 : ℝ) / 100000000000000000) ≤ TailWholeCommonLog.coeffDP ∧ TailWholeCommonLog.coeffDP ≤ ((-1502476454899482357359 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.coeffDP_exact]
  constructor <;> nlinarith only [root_bounds.1, root_bounds.2]

theorem constant0_bounds :
    ((-707354006672521223 : ℝ) / 10000000000000000) ≤ TailWholeCommonLog.rational ∧ TailWholeCommonLog.rational ≤ ((-70735400667252122299 : ℝ) / 1000000000000000000) := by
  rw [TailWholeCommonLog.rational_exact]
  norm_num

theorem constant1_bounds :
    ((4138036925717 : ℝ) / 1000000000000000000) ≤ EJoint.payment ∧ EJoint.payment ≤ ((2069018462859 : ℝ) / 500000000000000000) := by
  rw [WholeCommonLog.e_payment_exact]
  norm_num

end WuTarget.W10
