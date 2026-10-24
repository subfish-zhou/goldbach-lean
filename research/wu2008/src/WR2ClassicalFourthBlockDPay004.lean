import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay004
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_004 (j : Fin 64) (hj : 64*4+j.val < 2540) :
    DPay (64*4+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_256
  · exact WuPaper.ClassicalFourthNat.DPay_257
  · exact WuPaper.ClassicalFourthNat.DPay_258
  · exact WuPaper.ClassicalFourthNat.DPay_259
  · exact WuPaper.ClassicalFourthNat.DPay_260
  · exact WuPaper.ClassicalFourthNat.DPay_261
  · exact WuPaper.ClassicalFourthNat.DPay_262
  · exact WuPaper.ClassicalFourthNat.DPay_263
  · exact WuPaper.ClassicalFourthNat.DPay_264
  · exact WuPaper.ClassicalFourthNat.DPay_265
  · exact WuPaper.ClassicalFourthNat.DPay_266
  · exact WuPaper.ClassicalFourthNat.DPay_267
  · exact WuPaper.ClassicalFourthNat.DPay_268
  · exact WuPaper.ClassicalFourthNat.DPay_269
  · exact WuPaper.ClassicalFourthNat.DPay_270
  · exact WuPaper.ClassicalFourthNat.DPay_271
  · exact WuPaper.ClassicalFourthNat.DPay_272
  · exact WuPaper.ClassicalFourthNat.DPay_273
  · exact WuPaper.ClassicalFourthNat.DPay_274
  · exact WuPaper.ClassicalFourthNat.DPay_275
  · exact WuPaper.ClassicalFourthNat.DPay_276
  · exact WuPaper.ClassicalFourthNat.DPay_277
  · exact WuPaper.ClassicalFourthNat.DPay_278
  · exact WuPaper.ClassicalFourthNat.DPay_279
  · exact WuPaper.ClassicalFourthNat.DPay_280
  · exact WuPaper.ClassicalFourthNat.DPay_281
  · exact WuPaper.ClassicalFourthNat.DPay_282
  · exact WuPaper.ClassicalFourthNat.DPay_283
  · exact WuPaper.ClassicalFourthNat.DPay_284
  · exact WuPaper.ClassicalFourthNat.DPay_285
  · exact WuPaper.ClassicalFourthNat.DPay_286
  · exact WuPaper.ClassicalFourthNat.DPay_287
  · exact WuPaper.ClassicalFourthNat.DPay_288
  · exact WuPaper.ClassicalFourthNat.DPay_289
  · exact WuPaper.ClassicalFourthNat.DPay_290
  · exact WuPaper.ClassicalFourthNat.DPay_291
  · exact WuPaper.ClassicalFourthNat.DPay_292
  · exact WuPaper.ClassicalFourthNat.DPay_293
  · exact WuPaper.ClassicalFourthNat.DPay_294
  · exact WuPaper.ClassicalFourthNat.DPay_295
  · exact WuPaper.ClassicalFourthNat.DPay_296
  · exact WuPaper.ClassicalFourthNat.DPay_297
  · exact WuPaper.ClassicalFourthNat.DPay_298
  · exact WuPaper.ClassicalFourthNat.DPay_299
  · exact WuPaper.ClassicalFourthNat.DPay_300
  · exact WuPaper.ClassicalFourthNat.DPay_301
  · exact WuPaper.ClassicalFourthNat.DPay_302
  · exact WuPaper.ClassicalFourthNat.DPay_303
  · exact WuPaper.ClassicalFourthNat.DPay_304
  · exact WuPaper.ClassicalFourthNat.DPay_305
  · exact WuPaper.ClassicalFourthNat.DPay_306
  · exact WuPaper.ClassicalFourthNat.DPay_307
  · exact WuPaper.ClassicalFourthNat.DPay_308
  · exact WuPaper.ClassicalFourthNat.DPay_309
  · exact WuPaper.ClassicalFourthNat.DPay_310
  · exact WuPaper.ClassicalFourthNat.DPay_311
  · exact WuPaper.ClassicalFourthNat.DPay_312
  · exact WuPaper.ClassicalFourthNat.DPay_313
  · exact WuPaper.ClassicalFourthNat.DPay_314
  · exact WuPaper.ClassicalFourthNat.DPay_315
  · exact WuPaper.ClassicalFourthNat.DPay_316
  · exact WuPaper.ClassicalFourthNat.DPay_317
  · exact WuPaper.ClassicalFourthNat.DPay_318
  · exact WuPaper.ClassicalFourthNat.DPay_319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_004
