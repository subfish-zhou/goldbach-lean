import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay003
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_003 (j : Fin 64) (hj : 64*3+j.val < 10540) :
    OuterPay (64*3+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_192
  · exact WuPaper.ClassicalFourthNat.outerPay_193
  · exact WuPaper.ClassicalFourthNat.outerPay_194
  · exact WuPaper.ClassicalFourthNat.outerPay_195
  · exact WuPaper.ClassicalFourthNat.outerPay_196
  · exact WuPaper.ClassicalFourthNat.outerPay_197
  · exact WuPaper.ClassicalFourthNat.outerPay_198
  · exact WuPaper.ClassicalFourthNat.outerPay_199
  · exact WuPaper.ClassicalFourthNat.outerPay_200
  · exact WuPaper.ClassicalFourthNat.outerPay_201
  · exact WuPaper.ClassicalFourthNat.outerPay_202
  · exact WuPaper.ClassicalFourthNat.outerPay_203
  · exact WuPaper.ClassicalFourthNat.outerPay_204
  · exact WuPaper.ClassicalFourthNat.outerPay_205
  · exact WuPaper.ClassicalFourthNat.outerPay_206
  · exact WuPaper.ClassicalFourthNat.outerPay_207
  · exact WuPaper.ClassicalFourthNat.outerPay_208
  · exact WuPaper.ClassicalFourthNat.outerPay_209
  · exact WuPaper.ClassicalFourthNat.outerPay_210
  · exact WuPaper.ClassicalFourthNat.outerPay_211
  · exact WuPaper.ClassicalFourthNat.outerPay_212
  · exact WuPaper.ClassicalFourthNat.outerPay_213
  · exact WuPaper.ClassicalFourthNat.outerPay_214
  · exact WuPaper.ClassicalFourthNat.outerPay_215
  · exact WuPaper.ClassicalFourthNat.outerPay_216
  · exact WuPaper.ClassicalFourthNat.outerPay_217
  · exact WuPaper.ClassicalFourthNat.outerPay_218
  · exact WuPaper.ClassicalFourthNat.outerPay_219
  · exact WuPaper.ClassicalFourthNat.outerPay_220
  · exact WuPaper.ClassicalFourthNat.outerPay_221
  · exact WuPaper.ClassicalFourthNat.outerPay_222
  · exact WuPaper.ClassicalFourthNat.outerPay_223
  · exact WuPaper.ClassicalFourthNat.outerPay_224
  · exact WuPaper.ClassicalFourthNat.outerPay_225
  · exact WuPaper.ClassicalFourthNat.outerPay_226
  · exact WuPaper.ClassicalFourthNat.outerPay_227
  · exact WuPaper.ClassicalFourthNat.outerPay_228
  · exact WuPaper.ClassicalFourthNat.outerPay_229
  · exact WuPaper.ClassicalFourthNat.outerPay_230
  · exact WuPaper.ClassicalFourthNat.outerPay_231
  · exact WuPaper.ClassicalFourthNat.outerPay_232
  · exact WuPaper.ClassicalFourthNat.outerPay_233
  · exact WuPaper.ClassicalFourthNat.outerPay_234
  · exact WuPaper.ClassicalFourthNat.outerPay_235
  · exact WuPaper.ClassicalFourthNat.outerPay_236
  · exact WuPaper.ClassicalFourthNat.outerPay_237
  · exact WuPaper.ClassicalFourthNat.outerPay_238
  · exact WuPaper.ClassicalFourthNat.outerPay_239
  · exact WuPaper.ClassicalFourthNat.outerPay_240
  · exact WuPaper.ClassicalFourthNat.outerPay_241
  · exact WuPaper.ClassicalFourthNat.outerPay_242
  · exact WuPaper.ClassicalFourthNat.outerPay_243
  · exact WuPaper.ClassicalFourthNat.outerPay_244
  · exact WuPaper.ClassicalFourthNat.outerPay_245
  · exact WuPaper.ClassicalFourthNat.outerPay_246
  · exact WuPaper.ClassicalFourthNat.outerPay_247
  · exact WuPaper.ClassicalFourthNat.outerPay_248
  · exact WuPaper.ClassicalFourthNat.outerPay_249
  · exact WuPaper.ClassicalFourthNat.outerPay_250
  · exact WuPaper.ClassicalFourthNat.outerPay_251
  · exact WuPaper.ClassicalFourthNat.outerPay_252
  · exact WuPaper.ClassicalFourthNat.outerPay_253
  · exact WuPaper.ClassicalFourthNat.outerPay_254
  · exact WuPaper.ClassicalFourthNat.outerPay_255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_003
