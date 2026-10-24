import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay004
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_004 (j : Fin 64) (hj : 64*4+j.val < 2540) :
    CPay (64*4+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_256
  · exact WuPaper.ClassicalFourthNat.CPay_257
  · exact WuPaper.ClassicalFourthNat.CPay_258
  · exact WuPaper.ClassicalFourthNat.CPay_259
  · exact WuPaper.ClassicalFourthNat.CPay_260
  · exact WuPaper.ClassicalFourthNat.CPay_261
  · exact WuPaper.ClassicalFourthNat.CPay_262
  · exact WuPaper.ClassicalFourthNat.CPay_263
  · exact WuPaper.ClassicalFourthNat.CPay_264
  · exact WuPaper.ClassicalFourthNat.CPay_265
  · exact WuPaper.ClassicalFourthNat.CPay_266
  · exact WuPaper.ClassicalFourthNat.CPay_267
  · exact WuPaper.ClassicalFourthNat.CPay_268
  · exact WuPaper.ClassicalFourthNat.CPay_269
  · exact WuPaper.ClassicalFourthNat.CPay_270
  · exact WuPaper.ClassicalFourthNat.CPay_271
  · exact WuPaper.ClassicalFourthNat.CPay_272
  · exact WuPaper.ClassicalFourthNat.CPay_273
  · exact WuPaper.ClassicalFourthNat.CPay_274
  · exact WuPaper.ClassicalFourthNat.CPay_275
  · exact WuPaper.ClassicalFourthNat.CPay_276
  · exact WuPaper.ClassicalFourthNat.CPay_277
  · exact WuPaper.ClassicalFourthNat.CPay_278
  · exact WuPaper.ClassicalFourthNat.CPay_279
  · exact WuPaper.ClassicalFourthNat.CPay_280
  · exact WuPaper.ClassicalFourthNat.CPay_281
  · exact WuPaper.ClassicalFourthNat.CPay_282
  · exact WuPaper.ClassicalFourthNat.CPay_283
  · exact WuPaper.ClassicalFourthNat.CPay_284
  · exact WuPaper.ClassicalFourthNat.CPay_285
  · exact WuPaper.ClassicalFourthNat.CPay_286
  · exact WuPaper.ClassicalFourthNat.CPay_287
  · exact WuPaper.ClassicalFourthNat.CPay_288
  · exact WuPaper.ClassicalFourthNat.CPay_289
  · exact WuPaper.ClassicalFourthNat.CPay_290
  · exact WuPaper.ClassicalFourthNat.CPay_291
  · exact WuPaper.ClassicalFourthNat.CPay_292
  · exact WuPaper.ClassicalFourthNat.CPay_293
  · exact WuPaper.ClassicalFourthNat.CPay_294
  · exact WuPaper.ClassicalFourthNat.CPay_295
  · exact WuPaper.ClassicalFourthNat.CPay_296
  · exact WuPaper.ClassicalFourthNat.CPay_297
  · exact WuPaper.ClassicalFourthNat.CPay_298
  · exact WuPaper.ClassicalFourthNat.CPay_299
  · exact WuPaper.ClassicalFourthNat.CPay_300
  · exact WuPaper.ClassicalFourthNat.CPay_301
  · exact WuPaper.ClassicalFourthNat.CPay_302
  · exact WuPaper.ClassicalFourthNat.CPay_303
  · exact WuPaper.ClassicalFourthNat.CPay_304
  · exact WuPaper.ClassicalFourthNat.CPay_305
  · exact WuPaper.ClassicalFourthNat.CPay_306
  · exact WuPaper.ClassicalFourthNat.CPay_307
  · exact WuPaper.ClassicalFourthNat.CPay_308
  · exact WuPaper.ClassicalFourthNat.CPay_309
  · exact WuPaper.ClassicalFourthNat.CPay_310
  · exact WuPaper.ClassicalFourthNat.CPay_311
  · exact WuPaper.ClassicalFourthNat.CPay_312
  · exact WuPaper.ClassicalFourthNat.CPay_313
  · exact WuPaper.ClassicalFourthNat.CPay_314
  · exact WuPaper.ClassicalFourthNat.CPay_315
  · exact WuPaper.ClassicalFourthNat.CPay_316
  · exact WuPaper.ClassicalFourthNat.CPay_317
  · exact WuPaper.ClassicalFourthNat.CPay_318
  · exact WuPaper.ClassicalFourthNat.CPay_319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_004
