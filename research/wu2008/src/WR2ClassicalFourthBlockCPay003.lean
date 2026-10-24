import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay003
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_003 (j : Fin 64) (hj : 64*3+j.val < 2540) :
    CPay (64*3+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_192
  · exact WuPaper.ClassicalFourthNat.CPay_193
  · exact WuPaper.ClassicalFourthNat.CPay_194
  · exact WuPaper.ClassicalFourthNat.CPay_195
  · exact WuPaper.ClassicalFourthNat.CPay_196
  · exact WuPaper.ClassicalFourthNat.CPay_197
  · exact WuPaper.ClassicalFourthNat.CPay_198
  · exact WuPaper.ClassicalFourthNat.CPay_199
  · exact WuPaper.ClassicalFourthNat.CPay_200
  · exact WuPaper.ClassicalFourthNat.CPay_201
  · exact WuPaper.ClassicalFourthNat.CPay_202
  · exact WuPaper.ClassicalFourthNat.CPay_203
  · exact WuPaper.ClassicalFourthNat.CPay_204
  · exact WuPaper.ClassicalFourthNat.CPay_205
  · exact WuPaper.ClassicalFourthNat.CPay_206
  · exact WuPaper.ClassicalFourthNat.CPay_207
  · exact WuPaper.ClassicalFourthNat.CPay_208
  · exact WuPaper.ClassicalFourthNat.CPay_209
  · exact WuPaper.ClassicalFourthNat.CPay_210
  · exact WuPaper.ClassicalFourthNat.CPay_211
  · exact WuPaper.ClassicalFourthNat.CPay_212
  · exact WuPaper.ClassicalFourthNat.CPay_213
  · exact WuPaper.ClassicalFourthNat.CPay_214
  · exact WuPaper.ClassicalFourthNat.CPay_215
  · exact WuPaper.ClassicalFourthNat.CPay_216
  · exact WuPaper.ClassicalFourthNat.CPay_217
  · exact WuPaper.ClassicalFourthNat.CPay_218
  · exact WuPaper.ClassicalFourthNat.CPay_219
  · exact WuPaper.ClassicalFourthNat.CPay_220
  · exact WuPaper.ClassicalFourthNat.CPay_221
  · exact WuPaper.ClassicalFourthNat.CPay_222
  · exact WuPaper.ClassicalFourthNat.CPay_223
  · exact WuPaper.ClassicalFourthNat.CPay_224
  · exact WuPaper.ClassicalFourthNat.CPay_225
  · exact WuPaper.ClassicalFourthNat.CPay_226
  · exact WuPaper.ClassicalFourthNat.CPay_227
  · exact WuPaper.ClassicalFourthNat.CPay_228
  · exact WuPaper.ClassicalFourthNat.CPay_229
  · exact WuPaper.ClassicalFourthNat.CPay_230
  · exact WuPaper.ClassicalFourthNat.CPay_231
  · exact WuPaper.ClassicalFourthNat.CPay_232
  · exact WuPaper.ClassicalFourthNat.CPay_233
  · exact WuPaper.ClassicalFourthNat.CPay_234
  · exact WuPaper.ClassicalFourthNat.CPay_235
  · exact WuPaper.ClassicalFourthNat.CPay_236
  · exact WuPaper.ClassicalFourthNat.CPay_237
  · exact WuPaper.ClassicalFourthNat.CPay_238
  · exact WuPaper.ClassicalFourthNat.CPay_239
  · exact WuPaper.ClassicalFourthNat.CPay_240
  · exact WuPaper.ClassicalFourthNat.CPay_241
  · exact WuPaper.ClassicalFourthNat.CPay_242
  · exact WuPaper.ClassicalFourthNat.CPay_243
  · exact WuPaper.ClassicalFourthNat.CPay_244
  · exact WuPaper.ClassicalFourthNat.CPay_245
  · exact WuPaper.ClassicalFourthNat.CPay_246
  · exact WuPaper.ClassicalFourthNat.CPay_247
  · exact WuPaper.ClassicalFourthNat.CPay_248
  · exact WuPaper.ClassicalFourthNat.CPay_249
  · exact WuPaper.ClassicalFourthNat.CPay_250
  · exact WuPaper.ClassicalFourthNat.CPay_251
  · exact WuPaper.ClassicalFourthNat.CPay_252
  · exact WuPaper.ClassicalFourthNat.CPay_253
  · exact WuPaper.ClassicalFourthNat.CPay_254
  · exact WuPaper.ClassicalFourthNat.CPay_255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_003
