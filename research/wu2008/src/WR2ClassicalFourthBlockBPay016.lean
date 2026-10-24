import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay016
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_016 (j : Fin 64) (hj : 64*16+j.val < 10540) :
    BPay (64*16+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1024
  · exact WuPaper.ClassicalFourthNat.BPay_1025
  · exact WuPaper.ClassicalFourthNat.BPay_1026
  · exact WuPaper.ClassicalFourthNat.BPay_1027
  · exact WuPaper.ClassicalFourthNat.BPay_1028
  · exact WuPaper.ClassicalFourthNat.BPay_1029
  · exact WuPaper.ClassicalFourthNat.BPay_1030
  · exact WuPaper.ClassicalFourthNat.BPay_1031
  · exact WuPaper.ClassicalFourthNat.BPay_1032
  · exact WuPaper.ClassicalFourthNat.BPay_1033
  · exact WuPaper.ClassicalFourthNat.BPay_1034
  · exact WuPaper.ClassicalFourthNat.BPay_1035
  · exact WuPaper.ClassicalFourthNat.BPay_1036
  · exact WuPaper.ClassicalFourthNat.BPay_1037
  · exact WuPaper.ClassicalFourthNat.BPay_1038
  · exact WuPaper.ClassicalFourthNat.BPay_1039
  · exact WuPaper.ClassicalFourthNat.BPay_1040
  · exact WuPaper.ClassicalFourthNat.BPay_1041
  · exact WuPaper.ClassicalFourthNat.BPay_1042
  · exact WuPaper.ClassicalFourthNat.BPay_1043
  · exact WuPaper.ClassicalFourthNat.BPay_1044
  · exact WuPaper.ClassicalFourthNat.BPay_1045
  · exact WuPaper.ClassicalFourthNat.BPay_1046
  · exact WuPaper.ClassicalFourthNat.BPay_1047
  · exact WuPaper.ClassicalFourthNat.BPay_1048
  · exact WuPaper.ClassicalFourthNat.BPay_1049
  · exact WuPaper.ClassicalFourthNat.BPay_1050
  · exact WuPaper.ClassicalFourthNat.BPay_1051
  · exact WuPaper.ClassicalFourthNat.BPay_1052
  · exact WuPaper.ClassicalFourthNat.BPay_1053
  · exact WuPaper.ClassicalFourthNat.BPay_1054
  · exact WuPaper.ClassicalFourthNat.BPay_1055
  · exact WuPaper.ClassicalFourthNat.BPay_1056
  · exact WuPaper.ClassicalFourthNat.BPay_1057
  · exact WuPaper.ClassicalFourthNat.BPay_1058
  · exact WuPaper.ClassicalFourthNat.BPay_1059
  · exact WuPaper.ClassicalFourthNat.BPay_1060
  · exact WuPaper.ClassicalFourthNat.BPay_1061
  · exact WuPaper.ClassicalFourthNat.BPay_1062
  · exact WuPaper.ClassicalFourthNat.BPay_1063
  · exact WuPaper.ClassicalFourthNat.BPay_1064
  · exact WuPaper.ClassicalFourthNat.BPay_1065
  · exact WuPaper.ClassicalFourthNat.BPay_1066
  · exact WuPaper.ClassicalFourthNat.BPay_1067
  · exact WuPaper.ClassicalFourthNat.BPay_1068
  · exact WuPaper.ClassicalFourthNat.BPay_1069
  · exact WuPaper.ClassicalFourthNat.BPay_1070
  · exact WuPaper.ClassicalFourthNat.BPay_1071
  · exact WuPaper.ClassicalFourthNat.BPay_1072
  · exact WuPaper.ClassicalFourthNat.BPay_1073
  · exact WuPaper.ClassicalFourthNat.BPay_1074
  · exact WuPaper.ClassicalFourthNat.BPay_1075
  · exact WuPaper.ClassicalFourthNat.BPay_1076
  · exact WuPaper.ClassicalFourthNat.BPay_1077
  · exact WuPaper.ClassicalFourthNat.BPay_1078
  · exact WuPaper.ClassicalFourthNat.BPay_1079
  · exact WuPaper.ClassicalFourthNat.BPay_1080
  · exact WuPaper.ClassicalFourthNat.BPay_1081
  · exact WuPaper.ClassicalFourthNat.BPay_1082
  · exact WuPaper.ClassicalFourthNat.BPay_1083
  · exact WuPaper.ClassicalFourthNat.BPay_1084
  · exact WuPaper.ClassicalFourthNat.BPay_1085
  · exact WuPaper.ClassicalFourthNat.BPay_1086
  · exact WuPaper.ClassicalFourthNat.BPay_1087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_016
