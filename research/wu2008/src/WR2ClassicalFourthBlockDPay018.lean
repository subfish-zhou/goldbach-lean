import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay018
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_018 (j : Fin 64) (hj : 64*18+j.val < 2540) :
    DPay (64*18+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1152
  · exact WuPaper.ClassicalFourthNat.DPay_1153
  · exact WuPaper.ClassicalFourthNat.DPay_1154
  · exact WuPaper.ClassicalFourthNat.DPay_1155
  · exact WuPaper.ClassicalFourthNat.DPay_1156
  · exact WuPaper.ClassicalFourthNat.DPay_1157
  · exact WuPaper.ClassicalFourthNat.DPay_1158
  · exact WuPaper.ClassicalFourthNat.DPay_1159
  · exact WuPaper.ClassicalFourthNat.DPay_1160
  · exact WuPaper.ClassicalFourthNat.DPay_1161
  · exact WuPaper.ClassicalFourthNat.DPay_1162
  · exact WuPaper.ClassicalFourthNat.DPay_1163
  · exact WuPaper.ClassicalFourthNat.DPay_1164
  · exact WuPaper.ClassicalFourthNat.DPay_1165
  · exact WuPaper.ClassicalFourthNat.DPay_1166
  · exact WuPaper.ClassicalFourthNat.DPay_1167
  · exact WuPaper.ClassicalFourthNat.DPay_1168
  · exact WuPaper.ClassicalFourthNat.DPay_1169
  · exact WuPaper.ClassicalFourthNat.DPay_1170
  · exact WuPaper.ClassicalFourthNat.DPay_1171
  · exact WuPaper.ClassicalFourthNat.DPay_1172
  · exact WuPaper.ClassicalFourthNat.DPay_1173
  · exact WuPaper.ClassicalFourthNat.DPay_1174
  · exact WuPaper.ClassicalFourthNat.DPay_1175
  · exact WuPaper.ClassicalFourthNat.DPay_1176
  · exact WuPaper.ClassicalFourthNat.DPay_1177
  · exact WuPaper.ClassicalFourthNat.DPay_1178
  · exact WuPaper.ClassicalFourthNat.DPay_1179
  · exact WuPaper.ClassicalFourthNat.DPay_1180
  · exact WuPaper.ClassicalFourthNat.DPay_1181
  · exact WuPaper.ClassicalFourthNat.DPay_1182
  · exact WuPaper.ClassicalFourthNat.DPay_1183
  · exact WuPaper.ClassicalFourthNat.DPay_1184
  · exact WuPaper.ClassicalFourthNat.DPay_1185
  · exact WuPaper.ClassicalFourthNat.DPay_1186
  · exact WuPaper.ClassicalFourthNat.DPay_1187
  · exact WuPaper.ClassicalFourthNat.DPay_1188
  · exact WuPaper.ClassicalFourthNat.DPay_1189
  · exact WuPaper.ClassicalFourthNat.DPay_1190
  · exact WuPaper.ClassicalFourthNat.DPay_1191
  · exact WuPaper.ClassicalFourthNat.DPay_1192
  · exact WuPaper.ClassicalFourthNat.DPay_1193
  · exact WuPaper.ClassicalFourthNat.DPay_1194
  · exact WuPaper.ClassicalFourthNat.DPay_1195
  · exact WuPaper.ClassicalFourthNat.DPay_1196
  · exact WuPaper.ClassicalFourthNat.DPay_1197
  · exact WuPaper.ClassicalFourthNat.DPay_1198
  · exact WuPaper.ClassicalFourthNat.DPay_1199
  · exact WuPaper.ClassicalFourthNat.DPay_1200
  · exact WuPaper.ClassicalFourthNat.DPay_1201
  · exact WuPaper.ClassicalFourthNat.DPay_1202
  · exact WuPaper.ClassicalFourthNat.DPay_1203
  · exact WuPaper.ClassicalFourthNat.DPay_1204
  · exact WuPaper.ClassicalFourthNat.DPay_1205
  · exact WuPaper.ClassicalFourthNat.DPay_1206
  · exact WuPaper.ClassicalFourthNat.DPay_1207
  · exact WuPaper.ClassicalFourthNat.DPay_1208
  · exact WuPaper.ClassicalFourthNat.DPay_1209
  · exact WuPaper.ClassicalFourthNat.DPay_1210
  · exact WuPaper.ClassicalFourthNat.DPay_1211
  · exact WuPaper.ClassicalFourthNat.DPay_1212
  · exact WuPaper.ClassicalFourthNat.DPay_1213
  · exact WuPaper.ClassicalFourthNat.DPay_1214
  · exact WuPaper.ClassicalFourthNat.DPay_1215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_018
