import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay000
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_000 (j : Fin 64) (hj : 64*0+j.val < 2540) :
    CPay (64*0+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_0
  · exact WuPaper.ClassicalFourthNat.CPay_1
  · exact WuPaper.ClassicalFourthNat.CPay_2
  · exact WuPaper.ClassicalFourthNat.CPay_3
  · exact WuPaper.ClassicalFourthNat.CPay_4
  · exact WuPaper.ClassicalFourthNat.CPay_5
  · exact WuPaper.ClassicalFourthNat.CPay_6
  · exact WuPaper.ClassicalFourthNat.CPay_7
  · exact WuPaper.ClassicalFourthNat.CPay_8
  · exact WuPaper.ClassicalFourthNat.CPay_9
  · exact WuPaper.ClassicalFourthNat.CPay_10
  · exact WuPaper.ClassicalFourthNat.CPay_11
  · exact WuPaper.ClassicalFourthNat.CPay_12
  · exact WuPaper.ClassicalFourthNat.CPay_13
  · exact WuPaper.ClassicalFourthNat.CPay_14
  · exact WuPaper.ClassicalFourthNat.CPay_15
  · exact WuPaper.ClassicalFourthNat.CPay_16
  · exact WuPaper.ClassicalFourthNat.CPay_17
  · exact WuPaper.ClassicalFourthNat.CPay_18
  · exact WuPaper.ClassicalFourthNat.CPay_19
  · exact WuPaper.ClassicalFourthNat.CPay_20
  · exact WuPaper.ClassicalFourthNat.CPay_21
  · exact WuPaper.ClassicalFourthNat.CPay_22
  · exact WuPaper.ClassicalFourthNat.CPay_23
  · exact WuPaper.ClassicalFourthNat.CPay_24
  · exact WuPaper.ClassicalFourthNat.CPay_25
  · exact WuPaper.ClassicalFourthNat.CPay_26
  · exact WuPaper.ClassicalFourthNat.CPay_27
  · exact WuPaper.ClassicalFourthNat.CPay_28
  · exact WuPaper.ClassicalFourthNat.CPay_29
  · exact WuPaper.ClassicalFourthNat.CPay_30
  · exact WuPaper.ClassicalFourthNat.CPay_31
  · exact WuPaper.ClassicalFourthNat.CPay_32
  · exact WuPaper.ClassicalFourthNat.CPay_33
  · exact WuPaper.ClassicalFourthNat.CPay_34
  · exact WuPaper.ClassicalFourthNat.CPay_35
  · exact WuPaper.ClassicalFourthNat.CPay_36
  · exact WuPaper.ClassicalFourthNat.CPay_37
  · exact WuPaper.ClassicalFourthNat.CPay_38
  · exact WuPaper.ClassicalFourthNat.CPay_39
  · exact WuPaper.ClassicalFourthNat.CPay_40
  · exact WuPaper.ClassicalFourthNat.CPay_41
  · exact WuPaper.ClassicalFourthNat.CPay_42
  · exact WuPaper.ClassicalFourthNat.CPay_43
  · exact WuPaper.ClassicalFourthNat.CPay_44
  · exact WuPaper.ClassicalFourthNat.CPay_45
  · exact WuPaper.ClassicalFourthNat.CPay_46
  · exact WuPaper.ClassicalFourthNat.CPay_47
  · exact WuPaper.ClassicalFourthNat.CPay_48
  · exact WuPaper.ClassicalFourthNat.CPay_49
  · exact WuPaper.ClassicalFourthNat.CPay_50
  · exact WuPaper.ClassicalFourthNat.CPay_51
  · exact WuPaper.ClassicalFourthNat.CPay_52
  · exact WuPaper.ClassicalFourthNat.CPay_53
  · exact WuPaper.ClassicalFourthNat.CPay_54
  · exact WuPaper.ClassicalFourthNat.CPay_55
  · exact WuPaper.ClassicalFourthNat.CPay_56
  · exact WuPaper.ClassicalFourthNat.CPay_57
  · exact WuPaper.ClassicalFourthNat.CPay_58
  · exact WuPaper.ClassicalFourthNat.CPay_59
  · exact WuPaper.ClassicalFourthNat.CPay_60
  · exact WuPaper.ClassicalFourthNat.CPay_61
  · exact WuPaper.ClassicalFourthNat.CPay_62
  · exact WuPaper.ClassicalFourthNat.CPay_63
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_000
