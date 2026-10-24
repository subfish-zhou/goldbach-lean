import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay000
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_000 (j : Fin 64) (hj : 64*0+j.val < 2540) :
    DPay (64*0+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_0
  · exact WuPaper.ClassicalFourthNat.DPay_1
  · exact WuPaper.ClassicalFourthNat.DPay_2
  · exact WuPaper.ClassicalFourthNat.DPay_3
  · exact WuPaper.ClassicalFourthNat.DPay_4
  · exact WuPaper.ClassicalFourthNat.DPay_5
  · exact WuPaper.ClassicalFourthNat.DPay_6
  · exact WuPaper.ClassicalFourthNat.DPay_7
  · exact WuPaper.ClassicalFourthNat.DPay_8
  · exact WuPaper.ClassicalFourthNat.DPay_9
  · exact WuPaper.ClassicalFourthNat.DPay_10
  · exact WuPaper.ClassicalFourthNat.DPay_11
  · exact WuPaper.ClassicalFourthNat.DPay_12
  · exact WuPaper.ClassicalFourthNat.DPay_13
  · exact WuPaper.ClassicalFourthNat.DPay_14
  · exact WuPaper.ClassicalFourthNat.DPay_15
  · exact WuPaper.ClassicalFourthNat.DPay_16
  · exact WuPaper.ClassicalFourthNat.DPay_17
  · exact WuPaper.ClassicalFourthNat.DPay_18
  · exact WuPaper.ClassicalFourthNat.DPay_19
  · exact WuPaper.ClassicalFourthNat.DPay_20
  · exact WuPaper.ClassicalFourthNat.DPay_21
  · exact WuPaper.ClassicalFourthNat.DPay_22
  · exact WuPaper.ClassicalFourthNat.DPay_23
  · exact WuPaper.ClassicalFourthNat.DPay_24
  · exact WuPaper.ClassicalFourthNat.DPay_25
  · exact WuPaper.ClassicalFourthNat.DPay_26
  · exact WuPaper.ClassicalFourthNat.DPay_27
  · exact WuPaper.ClassicalFourthNat.DPay_28
  · exact WuPaper.ClassicalFourthNat.DPay_29
  · exact WuPaper.ClassicalFourthNat.DPay_30
  · exact WuPaper.ClassicalFourthNat.DPay_31
  · exact WuPaper.ClassicalFourthNat.DPay_32
  · exact WuPaper.ClassicalFourthNat.DPay_33
  · exact WuPaper.ClassicalFourthNat.DPay_34
  · exact WuPaper.ClassicalFourthNat.DPay_35
  · exact WuPaper.ClassicalFourthNat.DPay_36
  · exact WuPaper.ClassicalFourthNat.DPay_37
  · exact WuPaper.ClassicalFourthNat.DPay_38
  · exact WuPaper.ClassicalFourthNat.DPay_39
  · exact WuPaper.ClassicalFourthNat.DPay_40
  · exact WuPaper.ClassicalFourthNat.DPay_41
  · exact WuPaper.ClassicalFourthNat.DPay_42
  · exact WuPaper.ClassicalFourthNat.DPay_43
  · exact WuPaper.ClassicalFourthNat.DPay_44
  · exact WuPaper.ClassicalFourthNat.DPay_45
  · exact WuPaper.ClassicalFourthNat.DPay_46
  · exact WuPaper.ClassicalFourthNat.DPay_47
  · exact WuPaper.ClassicalFourthNat.DPay_48
  · exact WuPaper.ClassicalFourthNat.DPay_49
  · exact WuPaper.ClassicalFourthNat.DPay_50
  · exact WuPaper.ClassicalFourthNat.DPay_51
  · exact WuPaper.ClassicalFourthNat.DPay_52
  · exact WuPaper.ClassicalFourthNat.DPay_53
  · exact WuPaper.ClassicalFourthNat.DPay_54
  · exact WuPaper.ClassicalFourthNat.DPay_55
  · exact WuPaper.ClassicalFourthNat.DPay_56
  · exact WuPaper.ClassicalFourthNat.DPay_57
  · exact WuPaper.ClassicalFourthNat.DPay_58
  · exact WuPaper.ClassicalFourthNat.DPay_59
  · exact WuPaper.ClassicalFourthNat.DPay_60
  · exact WuPaper.ClassicalFourthNat.DPay_61
  · exact WuPaper.ClassicalFourthNat.DPay_62
  · exact WuPaper.ClassicalFourthNat.DPay_63
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_000
