import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_005 (j : Fin 64) (hj : 64*5+j.val < 2540) :
    CPay (64*5+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_320
  · exact WuPaper.ClassicalFourthNat.CPay_321
  · exact WuPaper.ClassicalFourthNat.CPay_322
  · exact WuPaper.ClassicalFourthNat.CPay_323
  · exact WuPaper.ClassicalFourthNat.CPay_324
  · exact WuPaper.ClassicalFourthNat.CPay_325
  · exact WuPaper.ClassicalFourthNat.CPay_326
  · exact WuPaper.ClassicalFourthNat.CPay_327
  · exact WuPaper.ClassicalFourthNat.CPay_328
  · exact WuPaper.ClassicalFourthNat.CPay_329
  · exact WuPaper.ClassicalFourthNat.CPay_330
  · exact WuPaper.ClassicalFourthNat.CPay_331
  · exact WuPaper.ClassicalFourthNat.CPay_332
  · exact WuPaper.ClassicalFourthNat.CPay_333
  · exact WuPaper.ClassicalFourthNat.CPay_334
  · exact WuPaper.ClassicalFourthNat.CPay_335
  · exact WuPaper.ClassicalFourthNat.CPay_336
  · exact WuPaper.ClassicalFourthNat.CPay_337
  · exact WuPaper.ClassicalFourthNat.CPay_338
  · exact WuPaper.ClassicalFourthNat.CPay_339
  · exact WuPaper.ClassicalFourthNat.CPay_340
  · exact WuPaper.ClassicalFourthNat.CPay_341
  · exact WuPaper.ClassicalFourthNat.CPay_342
  · exact WuPaper.ClassicalFourthNat.CPay_343
  · exact WuPaper.ClassicalFourthNat.CPay_344
  · exact WuPaper.ClassicalFourthNat.CPay_345
  · exact WuPaper.ClassicalFourthNat.CPay_346
  · exact WuPaper.ClassicalFourthNat.CPay_347
  · exact WuPaper.ClassicalFourthNat.CPay_348
  · exact WuPaper.ClassicalFourthNat.CPay_349
  · exact WuPaper.ClassicalFourthNat.CPay_350
  · exact WuPaper.ClassicalFourthNat.CPay_351
  · exact WuPaper.ClassicalFourthNat.CPay_352
  · exact WuPaper.ClassicalFourthNat.CPay_353
  · exact WuPaper.ClassicalFourthNat.CPay_354
  · exact WuPaper.ClassicalFourthNat.CPay_355
  · exact WuPaper.ClassicalFourthNat.CPay_356
  · exact WuPaper.ClassicalFourthNat.CPay_357
  · exact WuPaper.ClassicalFourthNat.CPay_358
  · exact WuPaper.ClassicalFourthNat.CPay_359
  · exact WuPaper.ClassicalFourthNat.CPay_360
  · exact WuPaper.ClassicalFourthNat.CPay_361
  · exact WuPaper.ClassicalFourthNat.CPay_362
  · exact WuPaper.ClassicalFourthNat.CPay_363
  · exact WuPaper.ClassicalFourthNat.CPay_364
  · exact WuPaper.ClassicalFourthNat.CPay_365
  · exact WuPaper.ClassicalFourthNat.CPay_366
  · exact WuPaper.ClassicalFourthNat.CPay_367
  · exact WuPaper.ClassicalFourthNat.CPay_368
  · exact WuPaper.ClassicalFourthNat.CPay_369
  · exact WuPaper.ClassicalFourthNat.CPay_370
  · exact WuPaper.ClassicalFourthNat.CPay_371
  · exact WuPaper.ClassicalFourthNat.CPay_372
  · exact WuPaper.ClassicalFourthNat.CPay_373
  · exact WuPaper.ClassicalFourthNat.CPay_374
  · exact WuPaper.ClassicalFourthNat.CPay_375
  · exact WuPaper.ClassicalFourthNat.CPay_376
  · exact WuPaper.ClassicalFourthNat.CPay_377
  · exact WuPaper.ClassicalFourthNat.CPay_378
  · exact WuPaper.ClassicalFourthNat.CPay_379
  · exact WuPaper.ClassicalFourthNat.CPay_380
  · exact WuPaper.ClassicalFourthNat.CPay_381
  · exact WuPaper.ClassicalFourthNat.CPay_382
  · exact WuPaper.ClassicalFourthNat.CPay_383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_005
