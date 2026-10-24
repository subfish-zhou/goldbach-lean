import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay017
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_017 (j : Fin 64) (hj : 64*17+j.val < 2540) :
    CPay (64*17+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1088
  · exact WuPaper.ClassicalFourthNat.CPay_1089
  · exact WuPaper.ClassicalFourthNat.CPay_1090
  · exact WuPaper.ClassicalFourthNat.CPay_1091
  · exact WuPaper.ClassicalFourthNat.CPay_1092
  · exact WuPaper.ClassicalFourthNat.CPay_1093
  · exact WuPaper.ClassicalFourthNat.CPay_1094
  · exact WuPaper.ClassicalFourthNat.CPay_1095
  · exact WuPaper.ClassicalFourthNat.CPay_1096
  · exact WuPaper.ClassicalFourthNat.CPay_1097
  · exact WuPaper.ClassicalFourthNat.CPay_1098
  · exact WuPaper.ClassicalFourthNat.CPay_1099
  · exact WuPaper.ClassicalFourthNat.CPay_1100
  · exact WuPaper.ClassicalFourthNat.CPay_1101
  · exact WuPaper.ClassicalFourthNat.CPay_1102
  · exact WuPaper.ClassicalFourthNat.CPay_1103
  · exact WuPaper.ClassicalFourthNat.CPay_1104
  · exact WuPaper.ClassicalFourthNat.CPay_1105
  · exact WuPaper.ClassicalFourthNat.CPay_1106
  · exact WuPaper.ClassicalFourthNat.CPay_1107
  · exact WuPaper.ClassicalFourthNat.CPay_1108
  · exact WuPaper.ClassicalFourthNat.CPay_1109
  · exact WuPaper.ClassicalFourthNat.CPay_1110
  · exact WuPaper.ClassicalFourthNat.CPay_1111
  · exact WuPaper.ClassicalFourthNat.CPay_1112
  · exact WuPaper.ClassicalFourthNat.CPay_1113
  · exact WuPaper.ClassicalFourthNat.CPay_1114
  · exact WuPaper.ClassicalFourthNat.CPay_1115
  · exact WuPaper.ClassicalFourthNat.CPay_1116
  · exact WuPaper.ClassicalFourthNat.CPay_1117
  · exact WuPaper.ClassicalFourthNat.CPay_1118
  · exact WuPaper.ClassicalFourthNat.CPay_1119
  · exact WuPaper.ClassicalFourthNat.CPay_1120
  · exact WuPaper.ClassicalFourthNat.CPay_1121
  · exact WuPaper.ClassicalFourthNat.CPay_1122
  · exact WuPaper.ClassicalFourthNat.CPay_1123
  · exact WuPaper.ClassicalFourthNat.CPay_1124
  · exact WuPaper.ClassicalFourthNat.CPay_1125
  · exact WuPaper.ClassicalFourthNat.CPay_1126
  · exact WuPaper.ClassicalFourthNat.CPay_1127
  · exact WuPaper.ClassicalFourthNat.CPay_1128
  · exact WuPaper.ClassicalFourthNat.CPay_1129
  · exact WuPaper.ClassicalFourthNat.CPay_1130
  · exact WuPaper.ClassicalFourthNat.CPay_1131
  · exact WuPaper.ClassicalFourthNat.CPay_1132
  · exact WuPaper.ClassicalFourthNat.CPay_1133
  · exact WuPaper.ClassicalFourthNat.CPay_1134
  · exact WuPaper.ClassicalFourthNat.CPay_1135
  · exact WuPaper.ClassicalFourthNat.CPay_1136
  · exact WuPaper.ClassicalFourthNat.CPay_1137
  · exact WuPaper.ClassicalFourthNat.CPay_1138
  · exact WuPaper.ClassicalFourthNat.CPay_1139
  · exact WuPaper.ClassicalFourthNat.CPay_1140
  · exact WuPaper.ClassicalFourthNat.CPay_1141
  · exact WuPaper.ClassicalFourthNat.CPay_1142
  · exact WuPaper.ClassicalFourthNat.CPay_1143
  · exact WuPaper.ClassicalFourthNat.CPay_1144
  · exact WuPaper.ClassicalFourthNat.CPay_1145
  · exact WuPaper.ClassicalFourthNat.CPay_1146
  · exact WuPaper.ClassicalFourthNat.CPay_1147
  · exact WuPaper.ClassicalFourthNat.CPay_1148
  · exact WuPaper.ClassicalFourthNat.CPay_1149
  · exact WuPaper.ClassicalFourthNat.CPay_1150
  · exact WuPaper.ClassicalFourthNat.CPay_1151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_017
