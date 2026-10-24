import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay018
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_018 (j : Fin 64) (hj : 64*18+j.val < 2540) :
    CPay (64*18+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1152
  · exact WuPaper.ClassicalFourthNat.CPay_1153
  · exact WuPaper.ClassicalFourthNat.CPay_1154
  · exact WuPaper.ClassicalFourthNat.CPay_1155
  · exact WuPaper.ClassicalFourthNat.CPay_1156
  · exact WuPaper.ClassicalFourthNat.CPay_1157
  · exact WuPaper.ClassicalFourthNat.CPay_1158
  · exact WuPaper.ClassicalFourthNat.CPay_1159
  · exact WuPaper.ClassicalFourthNat.CPay_1160
  · exact WuPaper.ClassicalFourthNat.CPay_1161
  · exact WuPaper.ClassicalFourthNat.CPay_1162
  · exact WuPaper.ClassicalFourthNat.CPay_1163
  · exact WuPaper.ClassicalFourthNat.CPay_1164
  · exact WuPaper.ClassicalFourthNat.CPay_1165
  · exact WuPaper.ClassicalFourthNat.CPay_1166
  · exact WuPaper.ClassicalFourthNat.CPay_1167
  · exact WuPaper.ClassicalFourthNat.CPay_1168
  · exact WuPaper.ClassicalFourthNat.CPay_1169
  · exact WuPaper.ClassicalFourthNat.CPay_1170
  · exact WuPaper.ClassicalFourthNat.CPay_1171
  · exact WuPaper.ClassicalFourthNat.CPay_1172
  · exact WuPaper.ClassicalFourthNat.CPay_1173
  · exact WuPaper.ClassicalFourthNat.CPay_1174
  · exact WuPaper.ClassicalFourthNat.CPay_1175
  · exact WuPaper.ClassicalFourthNat.CPay_1176
  · exact WuPaper.ClassicalFourthNat.CPay_1177
  · exact WuPaper.ClassicalFourthNat.CPay_1178
  · exact WuPaper.ClassicalFourthNat.CPay_1179
  · exact WuPaper.ClassicalFourthNat.CPay_1180
  · exact WuPaper.ClassicalFourthNat.CPay_1181
  · exact WuPaper.ClassicalFourthNat.CPay_1182
  · exact WuPaper.ClassicalFourthNat.CPay_1183
  · exact WuPaper.ClassicalFourthNat.CPay_1184
  · exact WuPaper.ClassicalFourthNat.CPay_1185
  · exact WuPaper.ClassicalFourthNat.CPay_1186
  · exact WuPaper.ClassicalFourthNat.CPay_1187
  · exact WuPaper.ClassicalFourthNat.CPay_1188
  · exact WuPaper.ClassicalFourthNat.CPay_1189
  · exact WuPaper.ClassicalFourthNat.CPay_1190
  · exact WuPaper.ClassicalFourthNat.CPay_1191
  · exact WuPaper.ClassicalFourthNat.CPay_1192
  · exact WuPaper.ClassicalFourthNat.CPay_1193
  · exact WuPaper.ClassicalFourthNat.CPay_1194
  · exact WuPaper.ClassicalFourthNat.CPay_1195
  · exact WuPaper.ClassicalFourthNat.CPay_1196
  · exact WuPaper.ClassicalFourthNat.CPay_1197
  · exact WuPaper.ClassicalFourthNat.CPay_1198
  · exact WuPaper.ClassicalFourthNat.CPay_1199
  · exact WuPaper.ClassicalFourthNat.CPay_1200
  · exact WuPaper.ClassicalFourthNat.CPay_1201
  · exact WuPaper.ClassicalFourthNat.CPay_1202
  · exact WuPaper.ClassicalFourthNat.CPay_1203
  · exact WuPaper.ClassicalFourthNat.CPay_1204
  · exact WuPaper.ClassicalFourthNat.CPay_1205
  · exact WuPaper.ClassicalFourthNat.CPay_1206
  · exact WuPaper.ClassicalFourthNat.CPay_1207
  · exact WuPaper.ClassicalFourthNat.CPay_1208
  · exact WuPaper.ClassicalFourthNat.CPay_1209
  · exact WuPaper.ClassicalFourthNat.CPay_1210
  · exact WuPaper.ClassicalFourthNat.CPay_1211
  · exact WuPaper.ClassicalFourthNat.CPay_1212
  · exact WuPaper.ClassicalFourthNat.CPay_1213
  · exact WuPaper.ClassicalFourthNat.CPay_1214
  · exact WuPaper.ClassicalFourthNat.CPay_1215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_018
