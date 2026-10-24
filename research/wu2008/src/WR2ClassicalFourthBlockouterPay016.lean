import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay016
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_016 (j : Fin 64) (hj : 64*16+j.val < 10540) :
    OuterPay (64*16+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1024
  · exact WuPaper.ClassicalFourthNat.outerPay_1025
  · exact WuPaper.ClassicalFourthNat.outerPay_1026
  · exact WuPaper.ClassicalFourthNat.outerPay_1027
  · exact WuPaper.ClassicalFourthNat.outerPay_1028
  · exact WuPaper.ClassicalFourthNat.outerPay_1029
  · exact WuPaper.ClassicalFourthNat.outerPay_1030
  · exact WuPaper.ClassicalFourthNat.outerPay_1031
  · exact WuPaper.ClassicalFourthNat.outerPay_1032
  · exact WuPaper.ClassicalFourthNat.outerPay_1033
  · exact WuPaper.ClassicalFourthNat.outerPay_1034
  · exact WuPaper.ClassicalFourthNat.outerPay_1035
  · exact WuPaper.ClassicalFourthNat.outerPay_1036
  · exact WuPaper.ClassicalFourthNat.outerPay_1037
  · exact WuPaper.ClassicalFourthNat.outerPay_1038
  · exact WuPaper.ClassicalFourthNat.outerPay_1039
  · exact WuPaper.ClassicalFourthNat.outerPay_1040
  · exact WuPaper.ClassicalFourthNat.outerPay_1041
  · exact WuPaper.ClassicalFourthNat.outerPay_1042
  · exact WuPaper.ClassicalFourthNat.outerPay_1043
  · exact WuPaper.ClassicalFourthNat.outerPay_1044
  · exact WuPaper.ClassicalFourthNat.outerPay_1045
  · exact WuPaper.ClassicalFourthNat.outerPay_1046
  · exact WuPaper.ClassicalFourthNat.outerPay_1047
  · exact WuPaper.ClassicalFourthNat.outerPay_1048
  · exact WuPaper.ClassicalFourthNat.outerPay_1049
  · exact WuPaper.ClassicalFourthNat.outerPay_1050
  · exact WuPaper.ClassicalFourthNat.outerPay_1051
  · exact WuPaper.ClassicalFourthNat.outerPay_1052
  · exact WuPaper.ClassicalFourthNat.outerPay_1053
  · exact WuPaper.ClassicalFourthNat.outerPay_1054
  · exact WuPaper.ClassicalFourthNat.outerPay_1055
  · exact WuPaper.ClassicalFourthNat.outerPay_1056
  · exact WuPaper.ClassicalFourthNat.outerPay_1057
  · exact WuPaper.ClassicalFourthNat.outerPay_1058
  · exact WuPaper.ClassicalFourthNat.outerPay_1059
  · exact WuPaper.ClassicalFourthNat.outerPay_1060
  · exact WuPaper.ClassicalFourthNat.outerPay_1061
  · exact WuPaper.ClassicalFourthNat.outerPay_1062
  · exact WuPaper.ClassicalFourthNat.outerPay_1063
  · exact WuPaper.ClassicalFourthNat.outerPay_1064
  · exact WuPaper.ClassicalFourthNat.outerPay_1065
  · exact WuPaper.ClassicalFourthNat.outerPay_1066
  · exact WuPaper.ClassicalFourthNat.outerPay_1067
  · exact WuPaper.ClassicalFourthNat.outerPay_1068
  · exact WuPaper.ClassicalFourthNat.outerPay_1069
  · exact WuPaper.ClassicalFourthNat.outerPay_1070
  · exact WuPaper.ClassicalFourthNat.outerPay_1071
  · exact WuPaper.ClassicalFourthNat.outerPay_1072
  · exact WuPaper.ClassicalFourthNat.outerPay_1073
  · exact WuPaper.ClassicalFourthNat.outerPay_1074
  · exact WuPaper.ClassicalFourthNat.outerPay_1075
  · exact WuPaper.ClassicalFourthNat.outerPay_1076
  · exact WuPaper.ClassicalFourthNat.outerPay_1077
  · exact WuPaper.ClassicalFourthNat.outerPay_1078
  · exact WuPaper.ClassicalFourthNat.outerPay_1079
  · exact WuPaper.ClassicalFourthNat.outerPay_1080
  · exact WuPaper.ClassicalFourthNat.outerPay_1081
  · exact WuPaper.ClassicalFourthNat.outerPay_1082
  · exact WuPaper.ClassicalFourthNat.outerPay_1083
  · exact WuPaper.ClassicalFourthNat.outerPay_1084
  · exact WuPaper.ClassicalFourthNat.outerPay_1085
  · exact WuPaper.ClassicalFourthNat.outerPay_1086
  · exact WuPaper.ClassicalFourthNat.outerPay_1087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_016
