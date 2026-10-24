import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay000
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_000 (j : Fin 64) (hj : 64*0+j.val < 10540) :
    BPay (64*0+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_0
  · exact WuPaper.ClassicalFourthNat.BPay_1
  · exact WuPaper.ClassicalFourthNat.BPay_2
  · exact WuPaper.ClassicalFourthNat.BPay_3
  · exact WuPaper.ClassicalFourthNat.BPay_4
  · exact WuPaper.ClassicalFourthNat.BPay_5
  · exact WuPaper.ClassicalFourthNat.BPay_6
  · exact WuPaper.ClassicalFourthNat.BPay_7
  · exact WuPaper.ClassicalFourthNat.BPay_8
  · exact WuPaper.ClassicalFourthNat.BPay_9
  · exact WuPaper.ClassicalFourthNat.BPay_10
  · exact WuPaper.ClassicalFourthNat.BPay_11
  · exact WuPaper.ClassicalFourthNat.BPay_12
  · exact WuPaper.ClassicalFourthNat.BPay_13
  · exact WuPaper.ClassicalFourthNat.BPay_14
  · exact WuPaper.ClassicalFourthNat.BPay_15
  · exact WuPaper.ClassicalFourthNat.BPay_16
  · exact WuPaper.ClassicalFourthNat.BPay_17
  · exact WuPaper.ClassicalFourthNat.BPay_18
  · exact WuPaper.ClassicalFourthNat.BPay_19
  · exact WuPaper.ClassicalFourthNat.BPay_20
  · exact WuPaper.ClassicalFourthNat.BPay_21
  · exact WuPaper.ClassicalFourthNat.BPay_22
  · exact WuPaper.ClassicalFourthNat.BPay_23
  · exact WuPaper.ClassicalFourthNat.BPay_24
  · exact WuPaper.ClassicalFourthNat.BPay_25
  · exact WuPaper.ClassicalFourthNat.BPay_26
  · exact WuPaper.ClassicalFourthNat.BPay_27
  · exact WuPaper.ClassicalFourthNat.BPay_28
  · exact WuPaper.ClassicalFourthNat.BPay_29
  · exact WuPaper.ClassicalFourthNat.BPay_30
  · exact WuPaper.ClassicalFourthNat.BPay_31
  · exact WuPaper.ClassicalFourthNat.BPay_32
  · exact WuPaper.ClassicalFourthNat.BPay_33
  · exact WuPaper.ClassicalFourthNat.BPay_34
  · exact WuPaper.ClassicalFourthNat.BPay_35
  · exact WuPaper.ClassicalFourthNat.BPay_36
  · exact WuPaper.ClassicalFourthNat.BPay_37
  · exact WuPaper.ClassicalFourthNat.BPay_38
  · exact WuPaper.ClassicalFourthNat.BPay_39
  · exact WuPaper.ClassicalFourthNat.BPay_40
  · exact WuPaper.ClassicalFourthNat.BPay_41
  · exact WuPaper.ClassicalFourthNat.BPay_42
  · exact WuPaper.ClassicalFourthNat.BPay_43
  · exact WuPaper.ClassicalFourthNat.BPay_44
  · exact WuPaper.ClassicalFourthNat.BPay_45
  · exact WuPaper.ClassicalFourthNat.BPay_46
  · exact WuPaper.ClassicalFourthNat.BPay_47
  · exact WuPaper.ClassicalFourthNat.BPay_48
  · exact WuPaper.ClassicalFourthNat.BPay_49
  · exact WuPaper.ClassicalFourthNat.BPay_50
  · exact WuPaper.ClassicalFourthNat.BPay_51
  · exact WuPaper.ClassicalFourthNat.BPay_52
  · exact WuPaper.ClassicalFourthNat.BPay_53
  · exact WuPaper.ClassicalFourthNat.BPay_54
  · exact WuPaper.ClassicalFourthNat.BPay_55
  · exact WuPaper.ClassicalFourthNat.BPay_56
  · exact WuPaper.ClassicalFourthNat.BPay_57
  · exact WuPaper.ClassicalFourthNat.BPay_58
  · exact WuPaper.ClassicalFourthNat.BPay_59
  · exact WuPaper.ClassicalFourthNat.BPay_60
  · exact WuPaper.ClassicalFourthNat.BPay_61
  · exact WuPaper.ClassicalFourthNat.BPay_62
  · exact WuPaper.ClassicalFourthNat.BPay_63
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_000
