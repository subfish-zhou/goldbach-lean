import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay004
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_004 (j : Fin 64) (hj : 64*4+j.val < 10540) :
    BPay (64*4+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_256
  · exact WuPaper.ClassicalFourthNat.BPay_257
  · exact WuPaper.ClassicalFourthNat.BPay_258
  · exact WuPaper.ClassicalFourthNat.BPay_259
  · exact WuPaper.ClassicalFourthNat.BPay_260
  · exact WuPaper.ClassicalFourthNat.BPay_261
  · exact WuPaper.ClassicalFourthNat.BPay_262
  · exact WuPaper.ClassicalFourthNat.BPay_263
  · exact WuPaper.ClassicalFourthNat.BPay_264
  · exact WuPaper.ClassicalFourthNat.BPay_265
  · exact WuPaper.ClassicalFourthNat.BPay_266
  · exact WuPaper.ClassicalFourthNat.BPay_267
  · exact WuPaper.ClassicalFourthNat.BPay_268
  · exact WuPaper.ClassicalFourthNat.BPay_269
  · exact WuPaper.ClassicalFourthNat.BPay_270
  · exact WuPaper.ClassicalFourthNat.BPay_271
  · exact WuPaper.ClassicalFourthNat.BPay_272
  · exact WuPaper.ClassicalFourthNat.BPay_273
  · exact WuPaper.ClassicalFourthNat.BPay_274
  · exact WuPaper.ClassicalFourthNat.BPay_275
  · exact WuPaper.ClassicalFourthNat.BPay_276
  · exact WuPaper.ClassicalFourthNat.BPay_277
  · exact WuPaper.ClassicalFourthNat.BPay_278
  · exact WuPaper.ClassicalFourthNat.BPay_279
  · exact WuPaper.ClassicalFourthNat.BPay_280
  · exact WuPaper.ClassicalFourthNat.BPay_281
  · exact WuPaper.ClassicalFourthNat.BPay_282
  · exact WuPaper.ClassicalFourthNat.BPay_283
  · exact WuPaper.ClassicalFourthNat.BPay_284
  · exact WuPaper.ClassicalFourthNat.BPay_285
  · exact WuPaper.ClassicalFourthNat.BPay_286
  · exact WuPaper.ClassicalFourthNat.BPay_287
  · exact WuPaper.ClassicalFourthNat.BPay_288
  · exact WuPaper.ClassicalFourthNat.BPay_289
  · exact WuPaper.ClassicalFourthNat.BPay_290
  · exact WuPaper.ClassicalFourthNat.BPay_291
  · exact WuPaper.ClassicalFourthNat.BPay_292
  · exact WuPaper.ClassicalFourthNat.BPay_293
  · exact WuPaper.ClassicalFourthNat.BPay_294
  · exact WuPaper.ClassicalFourthNat.BPay_295
  · exact WuPaper.ClassicalFourthNat.BPay_296
  · exact WuPaper.ClassicalFourthNat.BPay_297
  · exact WuPaper.ClassicalFourthNat.BPay_298
  · exact WuPaper.ClassicalFourthNat.BPay_299
  · exact WuPaper.ClassicalFourthNat.BPay_300
  · exact WuPaper.ClassicalFourthNat.BPay_301
  · exact WuPaper.ClassicalFourthNat.BPay_302
  · exact WuPaper.ClassicalFourthNat.BPay_303
  · exact WuPaper.ClassicalFourthNat.BPay_304
  · exact WuPaper.ClassicalFourthNat.BPay_305
  · exact WuPaper.ClassicalFourthNat.BPay_306
  · exact WuPaper.ClassicalFourthNat.BPay_307
  · exact WuPaper.ClassicalFourthNat.BPay_308
  · exact WuPaper.ClassicalFourthNat.BPay_309
  · exact WuPaper.ClassicalFourthNat.BPay_310
  · exact WuPaper.ClassicalFourthNat.BPay_311
  · exact WuPaper.ClassicalFourthNat.BPay_312
  · exact WuPaper.ClassicalFourthNat.BPay_313
  · exact WuPaper.ClassicalFourthNat.BPay_314
  · exact WuPaper.ClassicalFourthNat.BPay_315
  · exact WuPaper.ClassicalFourthNat.BPay_316
  · exact WuPaper.ClassicalFourthNat.BPay_317
  · exact WuPaper.ClassicalFourthNat.BPay_318
  · exact WuPaper.ClassicalFourthNat.BPay_319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_004
