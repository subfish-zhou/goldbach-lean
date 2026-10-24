import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay017
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_017 (j : Fin 64) (hj : 64*17+j.val < 10540) :
    BPay (64*17+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1088
  · exact WuPaper.ClassicalFourthNat.BPay_1089
  · exact WuPaper.ClassicalFourthNat.BPay_1090
  · exact WuPaper.ClassicalFourthNat.BPay_1091
  · exact WuPaper.ClassicalFourthNat.BPay_1092
  · exact WuPaper.ClassicalFourthNat.BPay_1093
  · exact WuPaper.ClassicalFourthNat.BPay_1094
  · exact WuPaper.ClassicalFourthNat.BPay_1095
  · exact WuPaper.ClassicalFourthNat.BPay_1096
  · exact WuPaper.ClassicalFourthNat.BPay_1097
  · exact WuPaper.ClassicalFourthNat.BPay_1098
  · exact WuPaper.ClassicalFourthNat.BPay_1099
  · exact WuPaper.ClassicalFourthNat.BPay_1100
  · exact WuPaper.ClassicalFourthNat.BPay_1101
  · exact WuPaper.ClassicalFourthNat.BPay_1102
  · exact WuPaper.ClassicalFourthNat.BPay_1103
  · exact WuPaper.ClassicalFourthNat.BPay_1104
  · exact WuPaper.ClassicalFourthNat.BPay_1105
  · exact WuPaper.ClassicalFourthNat.BPay_1106
  · exact WuPaper.ClassicalFourthNat.BPay_1107
  · exact WuPaper.ClassicalFourthNat.BPay_1108
  · exact WuPaper.ClassicalFourthNat.BPay_1109
  · exact WuPaper.ClassicalFourthNat.BPay_1110
  · exact WuPaper.ClassicalFourthNat.BPay_1111
  · exact WuPaper.ClassicalFourthNat.BPay_1112
  · exact WuPaper.ClassicalFourthNat.BPay_1113
  · exact WuPaper.ClassicalFourthNat.BPay_1114
  · exact WuPaper.ClassicalFourthNat.BPay_1115
  · exact WuPaper.ClassicalFourthNat.BPay_1116
  · exact WuPaper.ClassicalFourthNat.BPay_1117
  · exact WuPaper.ClassicalFourthNat.BPay_1118
  · exact WuPaper.ClassicalFourthNat.BPay_1119
  · exact WuPaper.ClassicalFourthNat.BPay_1120
  · exact WuPaper.ClassicalFourthNat.BPay_1121
  · exact WuPaper.ClassicalFourthNat.BPay_1122
  · exact WuPaper.ClassicalFourthNat.BPay_1123
  · exact WuPaper.ClassicalFourthNat.BPay_1124
  · exact WuPaper.ClassicalFourthNat.BPay_1125
  · exact WuPaper.ClassicalFourthNat.BPay_1126
  · exact WuPaper.ClassicalFourthNat.BPay_1127
  · exact WuPaper.ClassicalFourthNat.BPay_1128
  · exact WuPaper.ClassicalFourthNat.BPay_1129
  · exact WuPaper.ClassicalFourthNat.BPay_1130
  · exact WuPaper.ClassicalFourthNat.BPay_1131
  · exact WuPaper.ClassicalFourthNat.BPay_1132
  · exact WuPaper.ClassicalFourthNat.BPay_1133
  · exact WuPaper.ClassicalFourthNat.BPay_1134
  · exact WuPaper.ClassicalFourthNat.BPay_1135
  · exact WuPaper.ClassicalFourthNat.BPay_1136
  · exact WuPaper.ClassicalFourthNat.BPay_1137
  · exact WuPaper.ClassicalFourthNat.BPay_1138
  · exact WuPaper.ClassicalFourthNat.BPay_1139
  · exact WuPaper.ClassicalFourthNat.BPay_1140
  · exact WuPaper.ClassicalFourthNat.BPay_1141
  · exact WuPaper.ClassicalFourthNat.BPay_1142
  · exact WuPaper.ClassicalFourthNat.BPay_1143
  · exact WuPaper.ClassicalFourthNat.BPay_1144
  · exact WuPaper.ClassicalFourthNat.BPay_1145
  · exact WuPaper.ClassicalFourthNat.BPay_1146
  · exact WuPaper.ClassicalFourthNat.BPay_1147
  · exact WuPaper.ClassicalFourthNat.BPay_1148
  · exact WuPaper.ClassicalFourthNat.BPay_1149
  · exact WuPaper.ClassicalFourthNat.BPay_1150
  · exact WuPaper.ClassicalFourthNat.BPay_1151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_017
