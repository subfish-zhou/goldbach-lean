import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint000
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_000 (j : Fin 64) (hj : 64*0+j.val < 10541) :
    OuterPoint (64*0+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_0
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10
  · exact WuPaper.ClassicalFourthNat.OuterPoint_11
  · exact WuPaper.ClassicalFourthNat.OuterPoint_12
  · exact WuPaper.ClassicalFourthNat.OuterPoint_13
  · exact WuPaper.ClassicalFourthNat.OuterPoint_14
  · exact WuPaper.ClassicalFourthNat.OuterPoint_15
  · exact WuPaper.ClassicalFourthNat.OuterPoint_16
  · exact WuPaper.ClassicalFourthNat.OuterPoint_17
  · exact WuPaper.ClassicalFourthNat.OuterPoint_18
  · exact WuPaper.ClassicalFourthNat.OuterPoint_19
  · exact WuPaper.ClassicalFourthNat.OuterPoint_20
  · exact WuPaper.ClassicalFourthNat.OuterPoint_21
  · exact WuPaper.ClassicalFourthNat.OuterPoint_22
  · exact WuPaper.ClassicalFourthNat.OuterPoint_23
  · exact WuPaper.ClassicalFourthNat.OuterPoint_24
  · exact WuPaper.ClassicalFourthNat.OuterPoint_25
  · exact WuPaper.ClassicalFourthNat.OuterPoint_26
  · exact WuPaper.ClassicalFourthNat.OuterPoint_27
  · exact WuPaper.ClassicalFourthNat.OuterPoint_28
  · exact WuPaper.ClassicalFourthNat.OuterPoint_29
  · exact WuPaper.ClassicalFourthNat.OuterPoint_30
  · exact WuPaper.ClassicalFourthNat.OuterPoint_31
  · exact WuPaper.ClassicalFourthNat.OuterPoint_32
  · exact WuPaper.ClassicalFourthNat.OuterPoint_33
  · exact WuPaper.ClassicalFourthNat.OuterPoint_34
  · exact WuPaper.ClassicalFourthNat.OuterPoint_35
  · exact WuPaper.ClassicalFourthNat.OuterPoint_36
  · exact WuPaper.ClassicalFourthNat.OuterPoint_37
  · exact WuPaper.ClassicalFourthNat.OuterPoint_38
  · exact WuPaper.ClassicalFourthNat.OuterPoint_39
  · exact WuPaper.ClassicalFourthNat.OuterPoint_40
  · exact WuPaper.ClassicalFourthNat.OuterPoint_41
  · exact WuPaper.ClassicalFourthNat.OuterPoint_42
  · exact WuPaper.ClassicalFourthNat.OuterPoint_43
  · exact WuPaper.ClassicalFourthNat.OuterPoint_44
  · exact WuPaper.ClassicalFourthNat.OuterPoint_45
  · exact WuPaper.ClassicalFourthNat.OuterPoint_46
  · exact WuPaper.ClassicalFourthNat.OuterPoint_47
  · exact WuPaper.ClassicalFourthNat.OuterPoint_48
  · exact WuPaper.ClassicalFourthNat.OuterPoint_49
  · exact WuPaper.ClassicalFourthNat.OuterPoint_50
  · exact WuPaper.ClassicalFourthNat.OuterPoint_51
  · exact WuPaper.ClassicalFourthNat.OuterPoint_52
  · exact WuPaper.ClassicalFourthNat.OuterPoint_53
  · exact WuPaper.ClassicalFourthNat.OuterPoint_54
  · exact WuPaper.ClassicalFourthNat.OuterPoint_55
  · exact WuPaper.ClassicalFourthNat.OuterPoint_56
  · exact WuPaper.ClassicalFourthNat.OuterPoint_57
  · exact WuPaper.ClassicalFourthNat.OuterPoint_58
  · exact WuPaper.ClassicalFourthNat.OuterPoint_59
  · exact WuPaper.ClassicalFourthNat.OuterPoint_60
  · exact WuPaper.ClassicalFourthNat.OuterPoint_61
  · exact WuPaper.ClassicalFourthNat.OuterPoint_62
  · exact WuPaper.ClassicalFourthNat.OuterPoint_63
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_000
