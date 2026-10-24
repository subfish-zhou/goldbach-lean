import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay017
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_017 (j : Fin 64) (hj : 64*17+j.val < 2540) :
    DPay (64*17+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1088
  · exact WuPaper.ClassicalFourthNat.DPay_1089
  · exact WuPaper.ClassicalFourthNat.DPay_1090
  · exact WuPaper.ClassicalFourthNat.DPay_1091
  · exact WuPaper.ClassicalFourthNat.DPay_1092
  · exact WuPaper.ClassicalFourthNat.DPay_1093
  · exact WuPaper.ClassicalFourthNat.DPay_1094
  · exact WuPaper.ClassicalFourthNat.DPay_1095
  · exact WuPaper.ClassicalFourthNat.DPay_1096
  · exact WuPaper.ClassicalFourthNat.DPay_1097
  · exact WuPaper.ClassicalFourthNat.DPay_1098
  · exact WuPaper.ClassicalFourthNat.DPay_1099
  · exact WuPaper.ClassicalFourthNat.DPay_1100
  · exact WuPaper.ClassicalFourthNat.DPay_1101
  · exact WuPaper.ClassicalFourthNat.DPay_1102
  · exact WuPaper.ClassicalFourthNat.DPay_1103
  · exact WuPaper.ClassicalFourthNat.DPay_1104
  · exact WuPaper.ClassicalFourthNat.DPay_1105
  · exact WuPaper.ClassicalFourthNat.DPay_1106
  · exact WuPaper.ClassicalFourthNat.DPay_1107
  · exact WuPaper.ClassicalFourthNat.DPay_1108
  · exact WuPaper.ClassicalFourthNat.DPay_1109
  · exact WuPaper.ClassicalFourthNat.DPay_1110
  · exact WuPaper.ClassicalFourthNat.DPay_1111
  · exact WuPaper.ClassicalFourthNat.DPay_1112
  · exact WuPaper.ClassicalFourthNat.DPay_1113
  · exact WuPaper.ClassicalFourthNat.DPay_1114
  · exact WuPaper.ClassicalFourthNat.DPay_1115
  · exact WuPaper.ClassicalFourthNat.DPay_1116
  · exact WuPaper.ClassicalFourthNat.DPay_1117
  · exact WuPaper.ClassicalFourthNat.DPay_1118
  · exact WuPaper.ClassicalFourthNat.DPay_1119
  · exact WuPaper.ClassicalFourthNat.DPay_1120
  · exact WuPaper.ClassicalFourthNat.DPay_1121
  · exact WuPaper.ClassicalFourthNat.DPay_1122
  · exact WuPaper.ClassicalFourthNat.DPay_1123
  · exact WuPaper.ClassicalFourthNat.DPay_1124
  · exact WuPaper.ClassicalFourthNat.DPay_1125
  · exact WuPaper.ClassicalFourthNat.DPay_1126
  · exact WuPaper.ClassicalFourthNat.DPay_1127
  · exact WuPaper.ClassicalFourthNat.DPay_1128
  · exact WuPaper.ClassicalFourthNat.DPay_1129
  · exact WuPaper.ClassicalFourthNat.DPay_1130
  · exact WuPaper.ClassicalFourthNat.DPay_1131
  · exact WuPaper.ClassicalFourthNat.DPay_1132
  · exact WuPaper.ClassicalFourthNat.DPay_1133
  · exact WuPaper.ClassicalFourthNat.DPay_1134
  · exact WuPaper.ClassicalFourthNat.DPay_1135
  · exact WuPaper.ClassicalFourthNat.DPay_1136
  · exact WuPaper.ClassicalFourthNat.DPay_1137
  · exact WuPaper.ClassicalFourthNat.DPay_1138
  · exact WuPaper.ClassicalFourthNat.DPay_1139
  · exact WuPaper.ClassicalFourthNat.DPay_1140
  · exact WuPaper.ClassicalFourthNat.DPay_1141
  · exact WuPaper.ClassicalFourthNat.DPay_1142
  · exact WuPaper.ClassicalFourthNat.DPay_1143
  · exact WuPaper.ClassicalFourthNat.DPay_1144
  · exact WuPaper.ClassicalFourthNat.DPay_1145
  · exact WuPaper.ClassicalFourthNat.DPay_1146
  · exact WuPaper.ClassicalFourthNat.DPay_1147
  · exact WuPaper.ClassicalFourthNat.DPay_1148
  · exact WuPaper.ClassicalFourthNat.DPay_1149
  · exact WuPaper.ClassicalFourthNat.DPay_1150
  · exact WuPaper.ClassicalFourthNat.DPay_1151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_017
