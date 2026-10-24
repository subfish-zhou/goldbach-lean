import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay003
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_003 (j : Fin 64) (hj : 64*3+j.val < 2540) :
    DPay (64*3+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_192
  · exact WuPaper.ClassicalFourthNat.DPay_193
  · exact WuPaper.ClassicalFourthNat.DPay_194
  · exact WuPaper.ClassicalFourthNat.DPay_195
  · exact WuPaper.ClassicalFourthNat.DPay_196
  · exact WuPaper.ClassicalFourthNat.DPay_197
  · exact WuPaper.ClassicalFourthNat.DPay_198
  · exact WuPaper.ClassicalFourthNat.DPay_199
  · exact WuPaper.ClassicalFourthNat.DPay_200
  · exact WuPaper.ClassicalFourthNat.DPay_201
  · exact WuPaper.ClassicalFourthNat.DPay_202
  · exact WuPaper.ClassicalFourthNat.DPay_203
  · exact WuPaper.ClassicalFourthNat.DPay_204
  · exact WuPaper.ClassicalFourthNat.DPay_205
  · exact WuPaper.ClassicalFourthNat.DPay_206
  · exact WuPaper.ClassicalFourthNat.DPay_207
  · exact WuPaper.ClassicalFourthNat.DPay_208
  · exact WuPaper.ClassicalFourthNat.DPay_209
  · exact WuPaper.ClassicalFourthNat.DPay_210
  · exact WuPaper.ClassicalFourthNat.DPay_211
  · exact WuPaper.ClassicalFourthNat.DPay_212
  · exact WuPaper.ClassicalFourthNat.DPay_213
  · exact WuPaper.ClassicalFourthNat.DPay_214
  · exact WuPaper.ClassicalFourthNat.DPay_215
  · exact WuPaper.ClassicalFourthNat.DPay_216
  · exact WuPaper.ClassicalFourthNat.DPay_217
  · exact WuPaper.ClassicalFourthNat.DPay_218
  · exact WuPaper.ClassicalFourthNat.DPay_219
  · exact WuPaper.ClassicalFourthNat.DPay_220
  · exact WuPaper.ClassicalFourthNat.DPay_221
  · exact WuPaper.ClassicalFourthNat.DPay_222
  · exact WuPaper.ClassicalFourthNat.DPay_223
  · exact WuPaper.ClassicalFourthNat.DPay_224
  · exact WuPaper.ClassicalFourthNat.DPay_225
  · exact WuPaper.ClassicalFourthNat.DPay_226
  · exact WuPaper.ClassicalFourthNat.DPay_227
  · exact WuPaper.ClassicalFourthNat.DPay_228
  · exact WuPaper.ClassicalFourthNat.DPay_229
  · exact WuPaper.ClassicalFourthNat.DPay_230
  · exact WuPaper.ClassicalFourthNat.DPay_231
  · exact WuPaper.ClassicalFourthNat.DPay_232
  · exact WuPaper.ClassicalFourthNat.DPay_233
  · exact WuPaper.ClassicalFourthNat.DPay_234
  · exact WuPaper.ClassicalFourthNat.DPay_235
  · exact WuPaper.ClassicalFourthNat.DPay_236
  · exact WuPaper.ClassicalFourthNat.DPay_237
  · exact WuPaper.ClassicalFourthNat.DPay_238
  · exact WuPaper.ClassicalFourthNat.DPay_239
  · exact WuPaper.ClassicalFourthNat.DPay_240
  · exact WuPaper.ClassicalFourthNat.DPay_241
  · exact WuPaper.ClassicalFourthNat.DPay_242
  · exact WuPaper.ClassicalFourthNat.DPay_243
  · exact WuPaper.ClassicalFourthNat.DPay_244
  · exact WuPaper.ClassicalFourthNat.DPay_245
  · exact WuPaper.ClassicalFourthNat.DPay_246
  · exact WuPaper.ClassicalFourthNat.DPay_247
  · exact WuPaper.ClassicalFourthNat.DPay_248
  · exact WuPaper.ClassicalFourthNat.DPay_249
  · exact WuPaper.ClassicalFourthNat.DPay_250
  · exact WuPaper.ClassicalFourthNat.DPay_251
  · exact WuPaper.ClassicalFourthNat.DPay_252
  · exact WuPaper.ClassicalFourthNat.DPay_253
  · exact WuPaper.ClassicalFourthNat.DPay_254
  · exact WuPaper.ClassicalFourthNat.DPay_255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_003
