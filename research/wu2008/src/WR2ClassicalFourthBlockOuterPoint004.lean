import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint004
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_004 (j : Fin 64) (hj : 64*4+j.val < 10541) :
    OuterPoint (64*4+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_256
  · exact WuPaper.ClassicalFourthNat.OuterPoint_257
  · exact WuPaper.ClassicalFourthNat.OuterPoint_258
  · exact WuPaper.ClassicalFourthNat.OuterPoint_259
  · exact WuPaper.ClassicalFourthNat.OuterPoint_260
  · exact WuPaper.ClassicalFourthNat.OuterPoint_261
  · exact WuPaper.ClassicalFourthNat.OuterPoint_262
  · exact WuPaper.ClassicalFourthNat.OuterPoint_263
  · exact WuPaper.ClassicalFourthNat.OuterPoint_264
  · exact WuPaper.ClassicalFourthNat.OuterPoint_265
  · exact WuPaper.ClassicalFourthNat.OuterPoint_266
  · exact WuPaper.ClassicalFourthNat.OuterPoint_267
  · exact WuPaper.ClassicalFourthNat.OuterPoint_268
  · exact WuPaper.ClassicalFourthNat.OuterPoint_269
  · exact WuPaper.ClassicalFourthNat.OuterPoint_270
  · exact WuPaper.ClassicalFourthNat.OuterPoint_271
  · exact WuPaper.ClassicalFourthNat.OuterPoint_272
  · exact WuPaper.ClassicalFourthNat.OuterPoint_273
  · exact WuPaper.ClassicalFourthNat.OuterPoint_274
  · exact WuPaper.ClassicalFourthNat.OuterPoint_275
  · exact WuPaper.ClassicalFourthNat.OuterPoint_276
  · exact WuPaper.ClassicalFourthNat.OuterPoint_277
  · exact WuPaper.ClassicalFourthNat.OuterPoint_278
  · exact WuPaper.ClassicalFourthNat.OuterPoint_279
  · exact WuPaper.ClassicalFourthNat.OuterPoint_280
  · exact WuPaper.ClassicalFourthNat.OuterPoint_281
  · exact WuPaper.ClassicalFourthNat.OuterPoint_282
  · exact WuPaper.ClassicalFourthNat.OuterPoint_283
  · exact WuPaper.ClassicalFourthNat.OuterPoint_284
  · exact WuPaper.ClassicalFourthNat.OuterPoint_285
  · exact WuPaper.ClassicalFourthNat.OuterPoint_286
  · exact WuPaper.ClassicalFourthNat.OuterPoint_287
  · exact WuPaper.ClassicalFourthNat.OuterPoint_288
  · exact WuPaper.ClassicalFourthNat.OuterPoint_289
  · exact WuPaper.ClassicalFourthNat.OuterPoint_290
  · exact WuPaper.ClassicalFourthNat.OuterPoint_291
  · exact WuPaper.ClassicalFourthNat.OuterPoint_292
  · exact WuPaper.ClassicalFourthNat.OuterPoint_293
  · exact WuPaper.ClassicalFourthNat.OuterPoint_294
  · exact WuPaper.ClassicalFourthNat.OuterPoint_295
  · exact WuPaper.ClassicalFourthNat.OuterPoint_296
  · exact WuPaper.ClassicalFourthNat.OuterPoint_297
  · exact WuPaper.ClassicalFourthNat.OuterPoint_298
  · exact WuPaper.ClassicalFourthNat.OuterPoint_299
  · exact WuPaper.ClassicalFourthNat.OuterPoint_300
  · exact WuPaper.ClassicalFourthNat.OuterPoint_301
  · exact WuPaper.ClassicalFourthNat.OuterPoint_302
  · exact WuPaper.ClassicalFourthNat.OuterPoint_303
  · exact WuPaper.ClassicalFourthNat.OuterPoint_304
  · exact WuPaper.ClassicalFourthNat.OuterPoint_305
  · exact WuPaper.ClassicalFourthNat.OuterPoint_306
  · exact WuPaper.ClassicalFourthNat.OuterPoint_307
  · exact WuPaper.ClassicalFourthNat.OuterPoint_308
  · exact WuPaper.ClassicalFourthNat.OuterPoint_309
  · exact WuPaper.ClassicalFourthNat.OuterPoint_310
  · exact WuPaper.ClassicalFourthNat.OuterPoint_311
  · exact WuPaper.ClassicalFourthNat.OuterPoint_312
  · exact WuPaper.ClassicalFourthNat.OuterPoint_313
  · exact WuPaper.ClassicalFourthNat.OuterPoint_314
  · exact WuPaper.ClassicalFourthNat.OuterPoint_315
  · exact WuPaper.ClassicalFourthNat.OuterPoint_316
  · exact WuPaper.ClassicalFourthNat.OuterPoint_317
  · exact WuPaper.ClassicalFourthNat.OuterPoint_318
  · exact WuPaper.ClassicalFourthNat.OuterPoint_319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_004
