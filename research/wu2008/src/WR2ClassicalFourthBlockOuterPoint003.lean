import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint003
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_003 (j : Fin 64) (hj : 64*3+j.val < 10541) :
    OuterPoint (64*3+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_192
  · exact WuPaper.ClassicalFourthNat.OuterPoint_193
  · exact WuPaper.ClassicalFourthNat.OuterPoint_194
  · exact WuPaper.ClassicalFourthNat.OuterPoint_195
  · exact WuPaper.ClassicalFourthNat.OuterPoint_196
  · exact WuPaper.ClassicalFourthNat.OuterPoint_197
  · exact WuPaper.ClassicalFourthNat.OuterPoint_198
  · exact WuPaper.ClassicalFourthNat.OuterPoint_199
  · exact WuPaper.ClassicalFourthNat.OuterPoint_200
  · exact WuPaper.ClassicalFourthNat.OuterPoint_201
  · exact WuPaper.ClassicalFourthNat.OuterPoint_202
  · exact WuPaper.ClassicalFourthNat.OuterPoint_203
  · exact WuPaper.ClassicalFourthNat.OuterPoint_204
  · exact WuPaper.ClassicalFourthNat.OuterPoint_205
  · exact WuPaper.ClassicalFourthNat.OuterPoint_206
  · exact WuPaper.ClassicalFourthNat.OuterPoint_207
  · exact WuPaper.ClassicalFourthNat.OuterPoint_208
  · exact WuPaper.ClassicalFourthNat.OuterPoint_209
  · exact WuPaper.ClassicalFourthNat.OuterPoint_210
  · exact WuPaper.ClassicalFourthNat.OuterPoint_211
  · exact WuPaper.ClassicalFourthNat.OuterPoint_212
  · exact WuPaper.ClassicalFourthNat.OuterPoint_213
  · exact WuPaper.ClassicalFourthNat.OuterPoint_214
  · exact WuPaper.ClassicalFourthNat.OuterPoint_215
  · exact WuPaper.ClassicalFourthNat.OuterPoint_216
  · exact WuPaper.ClassicalFourthNat.OuterPoint_217
  · exact WuPaper.ClassicalFourthNat.OuterPoint_218
  · exact WuPaper.ClassicalFourthNat.OuterPoint_219
  · exact WuPaper.ClassicalFourthNat.OuterPoint_220
  · exact WuPaper.ClassicalFourthNat.OuterPoint_221
  · exact WuPaper.ClassicalFourthNat.OuterPoint_222
  · exact WuPaper.ClassicalFourthNat.OuterPoint_223
  · exact WuPaper.ClassicalFourthNat.OuterPoint_224
  · exact WuPaper.ClassicalFourthNat.OuterPoint_225
  · exact WuPaper.ClassicalFourthNat.OuterPoint_226
  · exact WuPaper.ClassicalFourthNat.OuterPoint_227
  · exact WuPaper.ClassicalFourthNat.OuterPoint_228
  · exact WuPaper.ClassicalFourthNat.OuterPoint_229
  · exact WuPaper.ClassicalFourthNat.OuterPoint_230
  · exact WuPaper.ClassicalFourthNat.OuterPoint_231
  · exact WuPaper.ClassicalFourthNat.OuterPoint_232
  · exact WuPaper.ClassicalFourthNat.OuterPoint_233
  · exact WuPaper.ClassicalFourthNat.OuterPoint_234
  · exact WuPaper.ClassicalFourthNat.OuterPoint_235
  · exact WuPaper.ClassicalFourthNat.OuterPoint_236
  · exact WuPaper.ClassicalFourthNat.OuterPoint_237
  · exact WuPaper.ClassicalFourthNat.OuterPoint_238
  · exact WuPaper.ClassicalFourthNat.OuterPoint_239
  · exact WuPaper.ClassicalFourthNat.OuterPoint_240
  · exact WuPaper.ClassicalFourthNat.OuterPoint_241
  · exact WuPaper.ClassicalFourthNat.OuterPoint_242
  · exact WuPaper.ClassicalFourthNat.OuterPoint_243
  · exact WuPaper.ClassicalFourthNat.OuterPoint_244
  · exact WuPaper.ClassicalFourthNat.OuterPoint_245
  · exact WuPaper.ClassicalFourthNat.OuterPoint_246
  · exact WuPaper.ClassicalFourthNat.OuterPoint_247
  · exact WuPaper.ClassicalFourthNat.OuterPoint_248
  · exact WuPaper.ClassicalFourthNat.OuterPoint_249
  · exact WuPaper.ClassicalFourthNat.OuterPoint_250
  · exact WuPaper.ClassicalFourthNat.OuterPoint_251
  · exact WuPaper.ClassicalFourthNat.OuterPoint_252
  · exact WuPaper.ClassicalFourthNat.OuterPoint_253
  · exact WuPaper.ClassicalFourthNat.OuterPoint_254
  · exact WuPaper.ClassicalFourthNat.OuterPoint_255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_003
