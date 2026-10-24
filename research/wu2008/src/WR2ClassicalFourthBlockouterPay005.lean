import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_005 (j : Fin 64) (hj : 64*5+j.val < 10540) :
    OuterPay (64*5+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_320
  · exact WuPaper.ClassicalFourthNat.outerPay_321
  · exact WuPaper.ClassicalFourthNat.outerPay_322
  · exact WuPaper.ClassicalFourthNat.outerPay_323
  · exact WuPaper.ClassicalFourthNat.outerPay_324
  · exact WuPaper.ClassicalFourthNat.outerPay_325
  · exact WuPaper.ClassicalFourthNat.outerPay_326
  · exact WuPaper.ClassicalFourthNat.outerPay_327
  · exact WuPaper.ClassicalFourthNat.outerPay_328
  · exact WuPaper.ClassicalFourthNat.outerPay_329
  · exact WuPaper.ClassicalFourthNat.outerPay_330
  · exact WuPaper.ClassicalFourthNat.outerPay_331
  · exact WuPaper.ClassicalFourthNat.outerPay_332
  · exact WuPaper.ClassicalFourthNat.outerPay_333
  · exact WuPaper.ClassicalFourthNat.outerPay_334
  · exact WuPaper.ClassicalFourthNat.outerPay_335
  · exact WuPaper.ClassicalFourthNat.outerPay_336
  · exact WuPaper.ClassicalFourthNat.outerPay_337
  · exact WuPaper.ClassicalFourthNat.outerPay_338
  · exact WuPaper.ClassicalFourthNat.outerPay_339
  · exact WuPaper.ClassicalFourthNat.outerPay_340
  · exact WuPaper.ClassicalFourthNat.outerPay_341
  · exact WuPaper.ClassicalFourthNat.outerPay_342
  · exact WuPaper.ClassicalFourthNat.outerPay_343
  · exact WuPaper.ClassicalFourthNat.outerPay_344
  · exact WuPaper.ClassicalFourthNat.outerPay_345
  · exact WuPaper.ClassicalFourthNat.outerPay_346
  · exact WuPaper.ClassicalFourthNat.outerPay_347
  · exact WuPaper.ClassicalFourthNat.outerPay_348
  · exact WuPaper.ClassicalFourthNat.outerPay_349
  · exact WuPaper.ClassicalFourthNat.outerPay_350
  · exact WuPaper.ClassicalFourthNat.outerPay_351
  · exact WuPaper.ClassicalFourthNat.outerPay_352
  · exact WuPaper.ClassicalFourthNat.outerPay_353
  · exact WuPaper.ClassicalFourthNat.outerPay_354
  · exact WuPaper.ClassicalFourthNat.outerPay_355
  · exact WuPaper.ClassicalFourthNat.outerPay_356
  · exact WuPaper.ClassicalFourthNat.outerPay_357
  · exact WuPaper.ClassicalFourthNat.outerPay_358
  · exact WuPaper.ClassicalFourthNat.outerPay_359
  · exact WuPaper.ClassicalFourthNat.outerPay_360
  · exact WuPaper.ClassicalFourthNat.outerPay_361
  · exact WuPaper.ClassicalFourthNat.outerPay_362
  · exact WuPaper.ClassicalFourthNat.outerPay_363
  · exact WuPaper.ClassicalFourthNat.outerPay_364
  · exact WuPaper.ClassicalFourthNat.outerPay_365
  · exact WuPaper.ClassicalFourthNat.outerPay_366
  · exact WuPaper.ClassicalFourthNat.outerPay_367
  · exact WuPaper.ClassicalFourthNat.outerPay_368
  · exact WuPaper.ClassicalFourthNat.outerPay_369
  · exact WuPaper.ClassicalFourthNat.outerPay_370
  · exact WuPaper.ClassicalFourthNat.outerPay_371
  · exact WuPaper.ClassicalFourthNat.outerPay_372
  · exact WuPaper.ClassicalFourthNat.outerPay_373
  · exact WuPaper.ClassicalFourthNat.outerPay_374
  · exact WuPaper.ClassicalFourthNat.outerPay_375
  · exact WuPaper.ClassicalFourthNat.outerPay_376
  · exact WuPaper.ClassicalFourthNat.outerPay_377
  · exact WuPaper.ClassicalFourthNat.outerPay_378
  · exact WuPaper.ClassicalFourthNat.outerPay_379
  · exact WuPaper.ClassicalFourthNat.outerPay_380
  · exact WuPaper.ClassicalFourthNat.outerPay_381
  · exact WuPaper.ClassicalFourthNat.outerPay_382
  · exact WuPaper.ClassicalFourthNat.outerPay_383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_005
