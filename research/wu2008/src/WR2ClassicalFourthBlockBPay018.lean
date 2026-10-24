import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay018
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_018 (j : Fin 64) (hj : 64*18+j.val < 10540) :
    BPay (64*18+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1152
  · exact WuPaper.ClassicalFourthNat.BPay_1153
  · exact WuPaper.ClassicalFourthNat.BPay_1154
  · exact WuPaper.ClassicalFourthNat.BPay_1155
  · exact WuPaper.ClassicalFourthNat.BPay_1156
  · exact WuPaper.ClassicalFourthNat.BPay_1157
  · exact WuPaper.ClassicalFourthNat.BPay_1158
  · exact WuPaper.ClassicalFourthNat.BPay_1159
  · exact WuPaper.ClassicalFourthNat.BPay_1160
  · exact WuPaper.ClassicalFourthNat.BPay_1161
  · exact WuPaper.ClassicalFourthNat.BPay_1162
  · exact WuPaper.ClassicalFourthNat.BPay_1163
  · exact WuPaper.ClassicalFourthNat.BPay_1164
  · exact WuPaper.ClassicalFourthNat.BPay_1165
  · exact WuPaper.ClassicalFourthNat.BPay_1166
  · exact WuPaper.ClassicalFourthNat.BPay_1167
  · exact WuPaper.ClassicalFourthNat.BPay_1168
  · exact WuPaper.ClassicalFourthNat.BPay_1169
  · exact WuPaper.ClassicalFourthNat.BPay_1170
  · exact WuPaper.ClassicalFourthNat.BPay_1171
  · exact WuPaper.ClassicalFourthNat.BPay_1172
  · exact WuPaper.ClassicalFourthNat.BPay_1173
  · exact WuPaper.ClassicalFourthNat.BPay_1174
  · exact WuPaper.ClassicalFourthNat.BPay_1175
  · exact WuPaper.ClassicalFourthNat.BPay_1176
  · exact WuPaper.ClassicalFourthNat.BPay_1177
  · exact WuPaper.ClassicalFourthNat.BPay_1178
  · exact WuPaper.ClassicalFourthNat.BPay_1179
  · exact WuPaper.ClassicalFourthNat.BPay_1180
  · exact WuPaper.ClassicalFourthNat.BPay_1181
  · exact WuPaper.ClassicalFourthNat.BPay_1182
  · exact WuPaper.ClassicalFourthNat.BPay_1183
  · exact WuPaper.ClassicalFourthNat.BPay_1184
  · exact WuPaper.ClassicalFourthNat.BPay_1185
  · exact WuPaper.ClassicalFourthNat.BPay_1186
  · exact WuPaper.ClassicalFourthNat.BPay_1187
  · exact WuPaper.ClassicalFourthNat.BPay_1188
  · exact WuPaper.ClassicalFourthNat.BPay_1189
  · exact WuPaper.ClassicalFourthNat.BPay_1190
  · exact WuPaper.ClassicalFourthNat.BPay_1191
  · exact WuPaper.ClassicalFourthNat.BPay_1192
  · exact WuPaper.ClassicalFourthNat.BPay_1193
  · exact WuPaper.ClassicalFourthNat.BPay_1194
  · exact WuPaper.ClassicalFourthNat.BPay_1195
  · exact WuPaper.ClassicalFourthNat.BPay_1196
  · exact WuPaper.ClassicalFourthNat.BPay_1197
  · exact WuPaper.ClassicalFourthNat.BPay_1198
  · exact WuPaper.ClassicalFourthNat.BPay_1199
  · exact WuPaper.ClassicalFourthNat.BPay_1200
  · exact WuPaper.ClassicalFourthNat.BPay_1201
  · exact WuPaper.ClassicalFourthNat.BPay_1202
  · exact WuPaper.ClassicalFourthNat.BPay_1203
  · exact WuPaper.ClassicalFourthNat.BPay_1204
  · exact WuPaper.ClassicalFourthNat.BPay_1205
  · exact WuPaper.ClassicalFourthNat.BPay_1206
  · exact WuPaper.ClassicalFourthNat.BPay_1207
  · exact WuPaper.ClassicalFourthNat.BPay_1208
  · exact WuPaper.ClassicalFourthNat.BPay_1209
  · exact WuPaper.ClassicalFourthNat.BPay_1210
  · exact WuPaper.ClassicalFourthNat.BPay_1211
  · exact WuPaper.ClassicalFourthNat.BPay_1212
  · exact WuPaper.ClassicalFourthNat.BPay_1213
  · exact WuPaper.ClassicalFourthNat.BPay_1214
  · exact WuPaper.ClassicalFourthNat.BPay_1215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_018
