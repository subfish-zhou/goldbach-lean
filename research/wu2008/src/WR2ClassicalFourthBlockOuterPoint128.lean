import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint128
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_128 (j : Fin 64) (hj : 64*128+j.val < 10541) :
    OuterPoint (64*128+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8192
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8193
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8194
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8195
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8196
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8197
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8198
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8199
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8200
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8201
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8202
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8203
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8204
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8205
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8206
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8207
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8208
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8209
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8210
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8211
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8212
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8213
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8214
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8215
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8216
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8217
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8218
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8219
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8220
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8221
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8222
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8223
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8224
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8225
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8226
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8227
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8228
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8229
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8230
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8231
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8232
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8233
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8234
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8235
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8236
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8237
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8238
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8239
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8240
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8241
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8242
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8243
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8244
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8245
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8246
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8247
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8248
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8249
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8250
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8251
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8252
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8253
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8254
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_128
