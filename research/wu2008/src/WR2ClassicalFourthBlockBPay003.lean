import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay003
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_003 (j : Fin 64) (hj : 64*3+j.val < 10540) :
    BPay (64*3+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_192
  · exact WuPaper.ClassicalFourthNat.BPay_193
  · exact WuPaper.ClassicalFourthNat.BPay_194
  · exact WuPaper.ClassicalFourthNat.BPay_195
  · exact WuPaper.ClassicalFourthNat.BPay_196
  · exact WuPaper.ClassicalFourthNat.BPay_197
  · exact WuPaper.ClassicalFourthNat.BPay_198
  · exact WuPaper.ClassicalFourthNat.BPay_199
  · exact WuPaper.ClassicalFourthNat.BPay_200
  · exact WuPaper.ClassicalFourthNat.BPay_201
  · exact WuPaper.ClassicalFourthNat.BPay_202
  · exact WuPaper.ClassicalFourthNat.BPay_203
  · exact WuPaper.ClassicalFourthNat.BPay_204
  · exact WuPaper.ClassicalFourthNat.BPay_205
  · exact WuPaper.ClassicalFourthNat.BPay_206
  · exact WuPaper.ClassicalFourthNat.BPay_207
  · exact WuPaper.ClassicalFourthNat.BPay_208
  · exact WuPaper.ClassicalFourthNat.BPay_209
  · exact WuPaper.ClassicalFourthNat.BPay_210
  · exact WuPaper.ClassicalFourthNat.BPay_211
  · exact WuPaper.ClassicalFourthNat.BPay_212
  · exact WuPaper.ClassicalFourthNat.BPay_213
  · exact WuPaper.ClassicalFourthNat.BPay_214
  · exact WuPaper.ClassicalFourthNat.BPay_215
  · exact WuPaper.ClassicalFourthNat.BPay_216
  · exact WuPaper.ClassicalFourthNat.BPay_217
  · exact WuPaper.ClassicalFourthNat.BPay_218
  · exact WuPaper.ClassicalFourthNat.BPay_219
  · exact WuPaper.ClassicalFourthNat.BPay_220
  · exact WuPaper.ClassicalFourthNat.BPay_221
  · exact WuPaper.ClassicalFourthNat.BPay_222
  · exact WuPaper.ClassicalFourthNat.BPay_223
  · exact WuPaper.ClassicalFourthNat.BPay_224
  · exact WuPaper.ClassicalFourthNat.BPay_225
  · exact WuPaper.ClassicalFourthNat.BPay_226
  · exact WuPaper.ClassicalFourthNat.BPay_227
  · exact WuPaper.ClassicalFourthNat.BPay_228
  · exact WuPaper.ClassicalFourthNat.BPay_229
  · exact WuPaper.ClassicalFourthNat.BPay_230
  · exact WuPaper.ClassicalFourthNat.BPay_231
  · exact WuPaper.ClassicalFourthNat.BPay_232
  · exact WuPaper.ClassicalFourthNat.BPay_233
  · exact WuPaper.ClassicalFourthNat.BPay_234
  · exact WuPaper.ClassicalFourthNat.BPay_235
  · exact WuPaper.ClassicalFourthNat.BPay_236
  · exact WuPaper.ClassicalFourthNat.BPay_237
  · exact WuPaper.ClassicalFourthNat.BPay_238
  · exact WuPaper.ClassicalFourthNat.BPay_239
  · exact WuPaper.ClassicalFourthNat.BPay_240
  · exact WuPaper.ClassicalFourthNat.BPay_241
  · exact WuPaper.ClassicalFourthNat.BPay_242
  · exact WuPaper.ClassicalFourthNat.BPay_243
  · exact WuPaper.ClassicalFourthNat.BPay_244
  · exact WuPaper.ClassicalFourthNat.BPay_245
  · exact WuPaper.ClassicalFourthNat.BPay_246
  · exact WuPaper.ClassicalFourthNat.BPay_247
  · exact WuPaper.ClassicalFourthNat.BPay_248
  · exact WuPaper.ClassicalFourthNat.BPay_249
  · exact WuPaper.ClassicalFourthNat.BPay_250
  · exact WuPaper.ClassicalFourthNat.BPay_251
  · exact WuPaper.ClassicalFourthNat.BPay_252
  · exact WuPaper.ClassicalFourthNat.BPay_253
  · exact WuPaper.ClassicalFourthNat.BPay_254
  · exact WuPaper.ClassicalFourthNat.BPay_255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_003
