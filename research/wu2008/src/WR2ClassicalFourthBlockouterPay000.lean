import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay000
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_000 (j : Fin 64) (hj : 64*0+j.val < 10540) :
    OuterPay (64*0+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_0
  · exact WuPaper.ClassicalFourthNat.outerPay_1
  · exact WuPaper.ClassicalFourthNat.outerPay_2
  · exact WuPaper.ClassicalFourthNat.outerPay_3
  · exact WuPaper.ClassicalFourthNat.outerPay_4
  · exact WuPaper.ClassicalFourthNat.outerPay_5
  · exact WuPaper.ClassicalFourthNat.outerPay_6
  · exact WuPaper.ClassicalFourthNat.outerPay_7
  · exact WuPaper.ClassicalFourthNat.outerPay_8
  · exact WuPaper.ClassicalFourthNat.outerPay_9
  · exact WuPaper.ClassicalFourthNat.outerPay_10
  · exact WuPaper.ClassicalFourthNat.outerPay_11
  · exact WuPaper.ClassicalFourthNat.outerPay_12
  · exact WuPaper.ClassicalFourthNat.outerPay_13
  · exact WuPaper.ClassicalFourthNat.outerPay_14
  · exact WuPaper.ClassicalFourthNat.outerPay_15
  · exact WuPaper.ClassicalFourthNat.outerPay_16
  · exact WuPaper.ClassicalFourthNat.outerPay_17
  · exact WuPaper.ClassicalFourthNat.outerPay_18
  · exact WuPaper.ClassicalFourthNat.outerPay_19
  · exact WuPaper.ClassicalFourthNat.outerPay_20
  · exact WuPaper.ClassicalFourthNat.outerPay_21
  · exact WuPaper.ClassicalFourthNat.outerPay_22
  · exact WuPaper.ClassicalFourthNat.outerPay_23
  · exact WuPaper.ClassicalFourthNat.outerPay_24
  · exact WuPaper.ClassicalFourthNat.outerPay_25
  · exact WuPaper.ClassicalFourthNat.outerPay_26
  · exact WuPaper.ClassicalFourthNat.outerPay_27
  · exact WuPaper.ClassicalFourthNat.outerPay_28
  · exact WuPaper.ClassicalFourthNat.outerPay_29
  · exact WuPaper.ClassicalFourthNat.outerPay_30
  · exact WuPaper.ClassicalFourthNat.outerPay_31
  · exact WuPaper.ClassicalFourthNat.outerPay_32
  · exact WuPaper.ClassicalFourthNat.outerPay_33
  · exact WuPaper.ClassicalFourthNat.outerPay_34
  · exact WuPaper.ClassicalFourthNat.outerPay_35
  · exact WuPaper.ClassicalFourthNat.outerPay_36
  · exact WuPaper.ClassicalFourthNat.outerPay_37
  · exact WuPaper.ClassicalFourthNat.outerPay_38
  · exact WuPaper.ClassicalFourthNat.outerPay_39
  · exact WuPaper.ClassicalFourthNat.outerPay_40
  · exact WuPaper.ClassicalFourthNat.outerPay_41
  · exact WuPaper.ClassicalFourthNat.outerPay_42
  · exact WuPaper.ClassicalFourthNat.outerPay_43
  · exact WuPaper.ClassicalFourthNat.outerPay_44
  · exact WuPaper.ClassicalFourthNat.outerPay_45
  · exact WuPaper.ClassicalFourthNat.outerPay_46
  · exact WuPaper.ClassicalFourthNat.outerPay_47
  · exact WuPaper.ClassicalFourthNat.outerPay_48
  · exact WuPaper.ClassicalFourthNat.outerPay_49
  · exact WuPaper.ClassicalFourthNat.outerPay_50
  · exact WuPaper.ClassicalFourthNat.outerPay_51
  · exact WuPaper.ClassicalFourthNat.outerPay_52
  · exact WuPaper.ClassicalFourthNat.outerPay_53
  · exact WuPaper.ClassicalFourthNat.outerPay_54
  · exact WuPaper.ClassicalFourthNat.outerPay_55
  · exact WuPaper.ClassicalFourthNat.outerPay_56
  · exact WuPaper.ClassicalFourthNat.outerPay_57
  · exact WuPaper.ClassicalFourthNat.outerPay_58
  · exact WuPaper.ClassicalFourthNat.outerPay_59
  · exact WuPaper.ClassicalFourthNat.outerPay_60
  · exact WuPaper.ClassicalFourthNat.outerPay_61
  · exact WuPaper.ClassicalFourthNat.outerPay_62
  · exact WuPaper.ClassicalFourthNat.outerPay_63
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_000
