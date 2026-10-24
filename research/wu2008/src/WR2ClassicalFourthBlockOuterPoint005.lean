import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_005 (j : Fin 64) (hj : 64*5+j.val < 10541) :
    OuterPoint (64*5+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_320
  · exact WuPaper.ClassicalFourthNat.OuterPoint_321
  · exact WuPaper.ClassicalFourthNat.OuterPoint_322
  · exact WuPaper.ClassicalFourthNat.OuterPoint_323
  · exact WuPaper.ClassicalFourthNat.OuterPoint_324
  · exact WuPaper.ClassicalFourthNat.OuterPoint_325
  · exact WuPaper.ClassicalFourthNat.OuterPoint_326
  · exact WuPaper.ClassicalFourthNat.OuterPoint_327
  · exact WuPaper.ClassicalFourthNat.OuterPoint_328
  · exact WuPaper.ClassicalFourthNat.OuterPoint_329
  · exact WuPaper.ClassicalFourthNat.OuterPoint_330
  · exact WuPaper.ClassicalFourthNat.OuterPoint_331
  · exact WuPaper.ClassicalFourthNat.OuterPoint_332
  · exact WuPaper.ClassicalFourthNat.OuterPoint_333
  · exact WuPaper.ClassicalFourthNat.OuterPoint_334
  · exact WuPaper.ClassicalFourthNat.OuterPoint_335
  · exact WuPaper.ClassicalFourthNat.OuterPoint_336
  · exact WuPaper.ClassicalFourthNat.OuterPoint_337
  · exact WuPaper.ClassicalFourthNat.OuterPoint_338
  · exact WuPaper.ClassicalFourthNat.OuterPoint_339
  · exact WuPaper.ClassicalFourthNat.OuterPoint_340
  · exact WuPaper.ClassicalFourthNat.OuterPoint_341
  · exact WuPaper.ClassicalFourthNat.OuterPoint_342
  · exact WuPaper.ClassicalFourthNat.OuterPoint_343
  · exact WuPaper.ClassicalFourthNat.OuterPoint_344
  · exact WuPaper.ClassicalFourthNat.OuterPoint_345
  · exact WuPaper.ClassicalFourthNat.OuterPoint_346
  · exact WuPaper.ClassicalFourthNat.OuterPoint_347
  · exact WuPaper.ClassicalFourthNat.OuterPoint_348
  · exact WuPaper.ClassicalFourthNat.OuterPoint_349
  · exact WuPaper.ClassicalFourthNat.OuterPoint_350
  · exact WuPaper.ClassicalFourthNat.OuterPoint_351
  · exact WuPaper.ClassicalFourthNat.OuterPoint_352
  · exact WuPaper.ClassicalFourthNat.OuterPoint_353
  · exact WuPaper.ClassicalFourthNat.OuterPoint_354
  · exact WuPaper.ClassicalFourthNat.OuterPoint_355
  · exact WuPaper.ClassicalFourthNat.OuterPoint_356
  · exact WuPaper.ClassicalFourthNat.OuterPoint_357
  · exact WuPaper.ClassicalFourthNat.OuterPoint_358
  · exact WuPaper.ClassicalFourthNat.OuterPoint_359
  · exact WuPaper.ClassicalFourthNat.OuterPoint_360
  · exact WuPaper.ClassicalFourthNat.OuterPoint_361
  · exact WuPaper.ClassicalFourthNat.OuterPoint_362
  · exact WuPaper.ClassicalFourthNat.OuterPoint_363
  · exact WuPaper.ClassicalFourthNat.OuterPoint_364
  · exact WuPaper.ClassicalFourthNat.OuterPoint_365
  · exact WuPaper.ClassicalFourthNat.OuterPoint_366
  · exact WuPaper.ClassicalFourthNat.OuterPoint_367
  · exact WuPaper.ClassicalFourthNat.OuterPoint_368
  · exact WuPaper.ClassicalFourthNat.OuterPoint_369
  · exact WuPaper.ClassicalFourthNat.OuterPoint_370
  · exact WuPaper.ClassicalFourthNat.OuterPoint_371
  · exact WuPaper.ClassicalFourthNat.OuterPoint_372
  · exact WuPaper.ClassicalFourthNat.OuterPoint_373
  · exact WuPaper.ClassicalFourthNat.OuterPoint_374
  · exact WuPaper.ClassicalFourthNat.OuterPoint_375
  · exact WuPaper.ClassicalFourthNat.OuterPoint_376
  · exact WuPaper.ClassicalFourthNat.OuterPoint_377
  · exact WuPaper.ClassicalFourthNat.OuterPoint_378
  · exact WuPaper.ClassicalFourthNat.OuterPoint_379
  · exact WuPaper.ClassicalFourthNat.OuterPoint_380
  · exact WuPaper.ClassicalFourthNat.OuterPoint_381
  · exact WuPaper.ClassicalFourthNat.OuterPoint_382
  · exact WuPaper.ClassicalFourthNat.OuterPoint_383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_005
