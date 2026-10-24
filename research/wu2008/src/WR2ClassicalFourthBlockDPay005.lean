import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_005 (j : Fin 64) (hj : 64*5+j.val < 2540) :
    DPay (64*5+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_320
  · exact WuPaper.ClassicalFourthNat.DPay_321
  · exact WuPaper.ClassicalFourthNat.DPay_322
  · exact WuPaper.ClassicalFourthNat.DPay_323
  · exact WuPaper.ClassicalFourthNat.DPay_324
  · exact WuPaper.ClassicalFourthNat.DPay_325
  · exact WuPaper.ClassicalFourthNat.DPay_326
  · exact WuPaper.ClassicalFourthNat.DPay_327
  · exact WuPaper.ClassicalFourthNat.DPay_328
  · exact WuPaper.ClassicalFourthNat.DPay_329
  · exact WuPaper.ClassicalFourthNat.DPay_330
  · exact WuPaper.ClassicalFourthNat.DPay_331
  · exact WuPaper.ClassicalFourthNat.DPay_332
  · exact WuPaper.ClassicalFourthNat.DPay_333
  · exact WuPaper.ClassicalFourthNat.DPay_334
  · exact WuPaper.ClassicalFourthNat.DPay_335
  · exact WuPaper.ClassicalFourthNat.DPay_336
  · exact WuPaper.ClassicalFourthNat.DPay_337
  · exact WuPaper.ClassicalFourthNat.DPay_338
  · exact WuPaper.ClassicalFourthNat.DPay_339
  · exact WuPaper.ClassicalFourthNat.DPay_340
  · exact WuPaper.ClassicalFourthNat.DPay_341
  · exact WuPaper.ClassicalFourthNat.DPay_342
  · exact WuPaper.ClassicalFourthNat.DPay_343
  · exact WuPaper.ClassicalFourthNat.DPay_344
  · exact WuPaper.ClassicalFourthNat.DPay_345
  · exact WuPaper.ClassicalFourthNat.DPay_346
  · exact WuPaper.ClassicalFourthNat.DPay_347
  · exact WuPaper.ClassicalFourthNat.DPay_348
  · exact WuPaper.ClassicalFourthNat.DPay_349
  · exact WuPaper.ClassicalFourthNat.DPay_350
  · exact WuPaper.ClassicalFourthNat.DPay_351
  · exact WuPaper.ClassicalFourthNat.DPay_352
  · exact WuPaper.ClassicalFourthNat.DPay_353
  · exact WuPaper.ClassicalFourthNat.DPay_354
  · exact WuPaper.ClassicalFourthNat.DPay_355
  · exact WuPaper.ClassicalFourthNat.DPay_356
  · exact WuPaper.ClassicalFourthNat.DPay_357
  · exact WuPaper.ClassicalFourthNat.DPay_358
  · exact WuPaper.ClassicalFourthNat.DPay_359
  · exact WuPaper.ClassicalFourthNat.DPay_360
  · exact WuPaper.ClassicalFourthNat.DPay_361
  · exact WuPaper.ClassicalFourthNat.DPay_362
  · exact WuPaper.ClassicalFourthNat.DPay_363
  · exact WuPaper.ClassicalFourthNat.DPay_364
  · exact WuPaper.ClassicalFourthNat.DPay_365
  · exact WuPaper.ClassicalFourthNat.DPay_366
  · exact WuPaper.ClassicalFourthNat.DPay_367
  · exact WuPaper.ClassicalFourthNat.DPay_368
  · exact WuPaper.ClassicalFourthNat.DPay_369
  · exact WuPaper.ClassicalFourthNat.DPay_370
  · exact WuPaper.ClassicalFourthNat.DPay_371
  · exact WuPaper.ClassicalFourthNat.DPay_372
  · exact WuPaper.ClassicalFourthNat.DPay_373
  · exact WuPaper.ClassicalFourthNat.DPay_374
  · exact WuPaper.ClassicalFourthNat.DPay_375
  · exact WuPaper.ClassicalFourthNat.DPay_376
  · exact WuPaper.ClassicalFourthNat.DPay_377
  · exact WuPaper.ClassicalFourthNat.DPay_378
  · exact WuPaper.ClassicalFourthNat.DPay_379
  · exact WuPaper.ClassicalFourthNat.DPay_380
  · exact WuPaper.ClassicalFourthNat.DPay_381
  · exact WuPaper.ClassicalFourthNat.DPay_382
  · exact WuPaper.ClassicalFourthNat.DPay_383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_005
