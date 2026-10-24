import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay016
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_016 (j : Fin 64) (hj : 64*16+j.val < 2540) :
    CPay (64*16+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1024
  · exact WuPaper.ClassicalFourthNat.CPay_1025
  · exact WuPaper.ClassicalFourthNat.CPay_1026
  · exact WuPaper.ClassicalFourthNat.CPay_1027
  · exact WuPaper.ClassicalFourthNat.CPay_1028
  · exact WuPaper.ClassicalFourthNat.CPay_1029
  · exact WuPaper.ClassicalFourthNat.CPay_1030
  · exact WuPaper.ClassicalFourthNat.CPay_1031
  · exact WuPaper.ClassicalFourthNat.CPay_1032
  · exact WuPaper.ClassicalFourthNat.CPay_1033
  · exact WuPaper.ClassicalFourthNat.CPay_1034
  · exact WuPaper.ClassicalFourthNat.CPay_1035
  · exact WuPaper.ClassicalFourthNat.CPay_1036
  · exact WuPaper.ClassicalFourthNat.CPay_1037
  · exact WuPaper.ClassicalFourthNat.CPay_1038
  · exact WuPaper.ClassicalFourthNat.CPay_1039
  · exact WuPaper.ClassicalFourthNat.CPay_1040
  · exact WuPaper.ClassicalFourthNat.CPay_1041
  · exact WuPaper.ClassicalFourthNat.CPay_1042
  · exact WuPaper.ClassicalFourthNat.CPay_1043
  · exact WuPaper.ClassicalFourthNat.CPay_1044
  · exact WuPaper.ClassicalFourthNat.CPay_1045
  · exact WuPaper.ClassicalFourthNat.CPay_1046
  · exact WuPaper.ClassicalFourthNat.CPay_1047
  · exact WuPaper.ClassicalFourthNat.CPay_1048
  · exact WuPaper.ClassicalFourthNat.CPay_1049
  · exact WuPaper.ClassicalFourthNat.CPay_1050
  · exact WuPaper.ClassicalFourthNat.CPay_1051
  · exact WuPaper.ClassicalFourthNat.CPay_1052
  · exact WuPaper.ClassicalFourthNat.CPay_1053
  · exact WuPaper.ClassicalFourthNat.CPay_1054
  · exact WuPaper.ClassicalFourthNat.CPay_1055
  · exact WuPaper.ClassicalFourthNat.CPay_1056
  · exact WuPaper.ClassicalFourthNat.CPay_1057
  · exact WuPaper.ClassicalFourthNat.CPay_1058
  · exact WuPaper.ClassicalFourthNat.CPay_1059
  · exact WuPaper.ClassicalFourthNat.CPay_1060
  · exact WuPaper.ClassicalFourthNat.CPay_1061
  · exact WuPaper.ClassicalFourthNat.CPay_1062
  · exact WuPaper.ClassicalFourthNat.CPay_1063
  · exact WuPaper.ClassicalFourthNat.CPay_1064
  · exact WuPaper.ClassicalFourthNat.CPay_1065
  · exact WuPaper.ClassicalFourthNat.CPay_1066
  · exact WuPaper.ClassicalFourthNat.CPay_1067
  · exact WuPaper.ClassicalFourthNat.CPay_1068
  · exact WuPaper.ClassicalFourthNat.CPay_1069
  · exact WuPaper.ClassicalFourthNat.CPay_1070
  · exact WuPaper.ClassicalFourthNat.CPay_1071
  · exact WuPaper.ClassicalFourthNat.CPay_1072
  · exact WuPaper.ClassicalFourthNat.CPay_1073
  · exact WuPaper.ClassicalFourthNat.CPay_1074
  · exact WuPaper.ClassicalFourthNat.CPay_1075
  · exact WuPaper.ClassicalFourthNat.CPay_1076
  · exact WuPaper.ClassicalFourthNat.CPay_1077
  · exact WuPaper.ClassicalFourthNat.CPay_1078
  · exact WuPaper.ClassicalFourthNat.CPay_1079
  · exact WuPaper.ClassicalFourthNat.CPay_1080
  · exact WuPaper.ClassicalFourthNat.CPay_1081
  · exact WuPaper.ClassicalFourthNat.CPay_1082
  · exact WuPaper.ClassicalFourthNat.CPay_1083
  · exact WuPaper.ClassicalFourthNat.CPay_1084
  · exact WuPaper.ClassicalFourthNat.CPay_1085
  · exact WuPaper.ClassicalFourthNat.CPay_1086
  · exact WuPaper.ClassicalFourthNat.CPay_1087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_016
