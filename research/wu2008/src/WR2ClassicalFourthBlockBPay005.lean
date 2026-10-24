import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_005 (j : Fin 64) (hj : 64*5+j.val < 10540) :
    BPay (64*5+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_320
  · exact WuPaper.ClassicalFourthNat.BPay_321
  · exact WuPaper.ClassicalFourthNat.BPay_322
  · exact WuPaper.ClassicalFourthNat.BPay_323
  · exact WuPaper.ClassicalFourthNat.BPay_324
  · exact WuPaper.ClassicalFourthNat.BPay_325
  · exact WuPaper.ClassicalFourthNat.BPay_326
  · exact WuPaper.ClassicalFourthNat.BPay_327
  · exact WuPaper.ClassicalFourthNat.BPay_328
  · exact WuPaper.ClassicalFourthNat.BPay_329
  · exact WuPaper.ClassicalFourthNat.BPay_330
  · exact WuPaper.ClassicalFourthNat.BPay_331
  · exact WuPaper.ClassicalFourthNat.BPay_332
  · exact WuPaper.ClassicalFourthNat.BPay_333
  · exact WuPaper.ClassicalFourthNat.BPay_334
  · exact WuPaper.ClassicalFourthNat.BPay_335
  · exact WuPaper.ClassicalFourthNat.BPay_336
  · exact WuPaper.ClassicalFourthNat.BPay_337
  · exact WuPaper.ClassicalFourthNat.BPay_338
  · exact WuPaper.ClassicalFourthNat.BPay_339
  · exact WuPaper.ClassicalFourthNat.BPay_340
  · exact WuPaper.ClassicalFourthNat.BPay_341
  · exact WuPaper.ClassicalFourthNat.BPay_342
  · exact WuPaper.ClassicalFourthNat.BPay_343
  · exact WuPaper.ClassicalFourthNat.BPay_344
  · exact WuPaper.ClassicalFourthNat.BPay_345
  · exact WuPaper.ClassicalFourthNat.BPay_346
  · exact WuPaper.ClassicalFourthNat.BPay_347
  · exact WuPaper.ClassicalFourthNat.BPay_348
  · exact WuPaper.ClassicalFourthNat.BPay_349
  · exact WuPaper.ClassicalFourthNat.BPay_350
  · exact WuPaper.ClassicalFourthNat.BPay_351
  · exact WuPaper.ClassicalFourthNat.BPay_352
  · exact WuPaper.ClassicalFourthNat.BPay_353
  · exact WuPaper.ClassicalFourthNat.BPay_354
  · exact WuPaper.ClassicalFourthNat.BPay_355
  · exact WuPaper.ClassicalFourthNat.BPay_356
  · exact WuPaper.ClassicalFourthNat.BPay_357
  · exact WuPaper.ClassicalFourthNat.BPay_358
  · exact WuPaper.ClassicalFourthNat.BPay_359
  · exact WuPaper.ClassicalFourthNat.BPay_360
  · exact WuPaper.ClassicalFourthNat.BPay_361
  · exact WuPaper.ClassicalFourthNat.BPay_362
  · exact WuPaper.ClassicalFourthNat.BPay_363
  · exact WuPaper.ClassicalFourthNat.BPay_364
  · exact WuPaper.ClassicalFourthNat.BPay_365
  · exact WuPaper.ClassicalFourthNat.BPay_366
  · exact WuPaper.ClassicalFourthNat.BPay_367
  · exact WuPaper.ClassicalFourthNat.BPay_368
  · exact WuPaper.ClassicalFourthNat.BPay_369
  · exact WuPaper.ClassicalFourthNat.BPay_370
  · exact WuPaper.ClassicalFourthNat.BPay_371
  · exact WuPaper.ClassicalFourthNat.BPay_372
  · exact WuPaper.ClassicalFourthNat.BPay_373
  · exact WuPaper.ClassicalFourthNat.BPay_374
  · exact WuPaper.ClassicalFourthNat.BPay_375
  · exact WuPaper.ClassicalFourthNat.BPay_376
  · exact WuPaper.ClassicalFourthNat.BPay_377
  · exact WuPaper.ClassicalFourthNat.BPay_378
  · exact WuPaper.ClassicalFourthNat.BPay_379
  · exact WuPaper.ClassicalFourthNat.BPay_380
  · exact WuPaper.ClassicalFourthNat.BPay_381
  · exact WuPaper.ClassicalFourthNat.BPay_382
  · exact WuPaper.ClassicalFourthNat.BPay_383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_005
