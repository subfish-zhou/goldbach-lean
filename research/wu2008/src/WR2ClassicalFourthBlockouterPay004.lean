import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay004
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_004 (j : Fin 64) (hj : 64*4+j.val < 10540) :
    OuterPay (64*4+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_256
  · exact WuPaper.ClassicalFourthNat.outerPay_257
  · exact WuPaper.ClassicalFourthNat.outerPay_258
  · exact WuPaper.ClassicalFourthNat.outerPay_259
  · exact WuPaper.ClassicalFourthNat.outerPay_260
  · exact WuPaper.ClassicalFourthNat.outerPay_261
  · exact WuPaper.ClassicalFourthNat.outerPay_262
  · exact WuPaper.ClassicalFourthNat.outerPay_263
  · exact WuPaper.ClassicalFourthNat.outerPay_264
  · exact WuPaper.ClassicalFourthNat.outerPay_265
  · exact WuPaper.ClassicalFourthNat.outerPay_266
  · exact WuPaper.ClassicalFourthNat.outerPay_267
  · exact WuPaper.ClassicalFourthNat.outerPay_268
  · exact WuPaper.ClassicalFourthNat.outerPay_269
  · exact WuPaper.ClassicalFourthNat.outerPay_270
  · exact WuPaper.ClassicalFourthNat.outerPay_271
  · exact WuPaper.ClassicalFourthNat.outerPay_272
  · exact WuPaper.ClassicalFourthNat.outerPay_273
  · exact WuPaper.ClassicalFourthNat.outerPay_274
  · exact WuPaper.ClassicalFourthNat.outerPay_275
  · exact WuPaper.ClassicalFourthNat.outerPay_276
  · exact WuPaper.ClassicalFourthNat.outerPay_277
  · exact WuPaper.ClassicalFourthNat.outerPay_278
  · exact WuPaper.ClassicalFourthNat.outerPay_279
  · exact WuPaper.ClassicalFourthNat.outerPay_280
  · exact WuPaper.ClassicalFourthNat.outerPay_281
  · exact WuPaper.ClassicalFourthNat.outerPay_282
  · exact WuPaper.ClassicalFourthNat.outerPay_283
  · exact WuPaper.ClassicalFourthNat.outerPay_284
  · exact WuPaper.ClassicalFourthNat.outerPay_285
  · exact WuPaper.ClassicalFourthNat.outerPay_286
  · exact WuPaper.ClassicalFourthNat.outerPay_287
  · exact WuPaper.ClassicalFourthNat.outerPay_288
  · exact WuPaper.ClassicalFourthNat.outerPay_289
  · exact WuPaper.ClassicalFourthNat.outerPay_290
  · exact WuPaper.ClassicalFourthNat.outerPay_291
  · exact WuPaper.ClassicalFourthNat.outerPay_292
  · exact WuPaper.ClassicalFourthNat.outerPay_293
  · exact WuPaper.ClassicalFourthNat.outerPay_294
  · exact WuPaper.ClassicalFourthNat.outerPay_295
  · exact WuPaper.ClassicalFourthNat.outerPay_296
  · exact WuPaper.ClassicalFourthNat.outerPay_297
  · exact WuPaper.ClassicalFourthNat.outerPay_298
  · exact WuPaper.ClassicalFourthNat.outerPay_299
  · exact WuPaper.ClassicalFourthNat.outerPay_300
  · exact WuPaper.ClassicalFourthNat.outerPay_301
  · exact WuPaper.ClassicalFourthNat.outerPay_302
  · exact WuPaper.ClassicalFourthNat.outerPay_303
  · exact WuPaper.ClassicalFourthNat.outerPay_304
  · exact WuPaper.ClassicalFourthNat.outerPay_305
  · exact WuPaper.ClassicalFourthNat.outerPay_306
  · exact WuPaper.ClassicalFourthNat.outerPay_307
  · exact WuPaper.ClassicalFourthNat.outerPay_308
  · exact WuPaper.ClassicalFourthNat.outerPay_309
  · exact WuPaper.ClassicalFourthNat.outerPay_310
  · exact WuPaper.ClassicalFourthNat.outerPay_311
  · exact WuPaper.ClassicalFourthNat.outerPay_312
  · exact WuPaper.ClassicalFourthNat.outerPay_313
  · exact WuPaper.ClassicalFourthNat.outerPay_314
  · exact WuPaper.ClassicalFourthNat.outerPay_315
  · exact WuPaper.ClassicalFourthNat.outerPay_316
  · exact WuPaper.ClassicalFourthNat.outerPay_317
  · exact WuPaper.ClassicalFourthNat.outerPay_318
  · exact WuPaper.ClassicalFourthNat.outerPay_319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_004
