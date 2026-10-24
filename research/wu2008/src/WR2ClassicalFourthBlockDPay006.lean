import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay006
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_006 (j : Fin 64) (hj : 64*6+j.val < 2540) :
    DPay (64*6+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_384
  · exact WuPaper.ClassicalFourthNat.DPay_385
  · exact WuPaper.ClassicalFourthNat.DPay_386
  · exact WuPaper.ClassicalFourthNat.DPay_387
  · exact WuPaper.ClassicalFourthNat.DPay_388
  · exact WuPaper.ClassicalFourthNat.DPay_389
  · exact WuPaper.ClassicalFourthNat.DPay_390
  · exact WuPaper.ClassicalFourthNat.DPay_391
  · exact WuPaper.ClassicalFourthNat.DPay_392
  · exact WuPaper.ClassicalFourthNat.DPay_393
  · exact WuPaper.ClassicalFourthNat.DPay_394
  · exact WuPaper.ClassicalFourthNat.DPay_395
  · exact WuPaper.ClassicalFourthNat.DPay_396
  · exact WuPaper.ClassicalFourthNat.DPay_397
  · exact WuPaper.ClassicalFourthNat.DPay_398
  · exact WuPaper.ClassicalFourthNat.DPay_399
  · exact WuPaper.ClassicalFourthNat.DPay_400
  · exact WuPaper.ClassicalFourthNat.DPay_401
  · exact WuPaper.ClassicalFourthNat.DPay_402
  · exact WuPaper.ClassicalFourthNat.DPay_403
  · exact WuPaper.ClassicalFourthNat.DPay_404
  · exact WuPaper.ClassicalFourthNat.DPay_405
  · exact WuPaper.ClassicalFourthNat.DPay_406
  · exact WuPaper.ClassicalFourthNat.DPay_407
  · exact WuPaper.ClassicalFourthNat.DPay_408
  · exact WuPaper.ClassicalFourthNat.DPay_409
  · exact WuPaper.ClassicalFourthNat.DPay_410
  · exact WuPaper.ClassicalFourthNat.DPay_411
  · exact WuPaper.ClassicalFourthNat.DPay_412
  · exact WuPaper.ClassicalFourthNat.DPay_413
  · exact WuPaper.ClassicalFourthNat.DPay_414
  · exact WuPaper.ClassicalFourthNat.DPay_415
  · exact WuPaper.ClassicalFourthNat.DPay_416
  · exact WuPaper.ClassicalFourthNat.DPay_417
  · exact WuPaper.ClassicalFourthNat.DPay_418
  · exact WuPaper.ClassicalFourthNat.DPay_419
  · exact WuPaper.ClassicalFourthNat.DPay_420
  · exact WuPaper.ClassicalFourthNat.DPay_421
  · exact WuPaper.ClassicalFourthNat.DPay_422
  · exact WuPaper.ClassicalFourthNat.DPay_423
  · exact WuPaper.ClassicalFourthNat.DPay_424
  · exact WuPaper.ClassicalFourthNat.DPay_425
  · exact WuPaper.ClassicalFourthNat.DPay_426
  · exact WuPaper.ClassicalFourthNat.DPay_427
  · exact WuPaper.ClassicalFourthNat.DPay_428
  · exact WuPaper.ClassicalFourthNat.DPay_429
  · exact WuPaper.ClassicalFourthNat.DPay_430
  · exact WuPaper.ClassicalFourthNat.DPay_431
  · exact WuPaper.ClassicalFourthNat.DPay_432
  · exact WuPaper.ClassicalFourthNat.DPay_433
  · exact WuPaper.ClassicalFourthNat.DPay_434
  · exact WuPaper.ClassicalFourthNat.DPay_435
  · exact WuPaper.ClassicalFourthNat.DPay_436
  · exact WuPaper.ClassicalFourthNat.DPay_437
  · exact WuPaper.ClassicalFourthNat.DPay_438
  · exact WuPaper.ClassicalFourthNat.DPay_439
  · exact WuPaper.ClassicalFourthNat.DPay_440
  · exact WuPaper.ClassicalFourthNat.DPay_441
  · exact WuPaper.ClassicalFourthNat.DPay_442
  · exact WuPaper.ClassicalFourthNat.DPay_443
  · exact WuPaper.ClassicalFourthNat.DPay_444
  · exact WuPaper.ClassicalFourthNat.DPay_445
  · exact WuPaper.ClassicalFourthNat.DPay_446
  · exact WuPaper.ClassicalFourthNat.DPay_447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_006
