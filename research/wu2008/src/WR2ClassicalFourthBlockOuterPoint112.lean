import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint112
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_112 (j : Fin 64) (hj : 64*112+j.val < 10541) :
    OuterPoint (64*112+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7168
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7169
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7170
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7171
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7172
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7173
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7174
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7175
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7176
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7177
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7178
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7179
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7180
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7181
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7182
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7183
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7184
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7185
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7186
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7187
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7188
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7189
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7190
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7191
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7192
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7193
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7194
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7195
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7196
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7197
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7198
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7199
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7200
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7201
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7202
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7203
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7204
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7205
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7206
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7207
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7208
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7209
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7210
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7211
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7212
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7213
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7214
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7215
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7216
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7217
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7218
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7219
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7220
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7221
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7222
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7223
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7224
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7225
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7226
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7227
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7228
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7229
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7230
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_112
