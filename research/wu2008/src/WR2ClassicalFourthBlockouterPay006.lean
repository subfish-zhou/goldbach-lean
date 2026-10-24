import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay006
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_006 (j : Fin 64) (hj : 64*6+j.val < 10540) :
    OuterPay (64*6+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_384
  · exact WuPaper.ClassicalFourthNat.outerPay_385
  · exact WuPaper.ClassicalFourthNat.outerPay_386
  · exact WuPaper.ClassicalFourthNat.outerPay_387
  · exact WuPaper.ClassicalFourthNat.outerPay_388
  · exact WuPaper.ClassicalFourthNat.outerPay_389
  · exact WuPaper.ClassicalFourthNat.outerPay_390
  · exact WuPaper.ClassicalFourthNat.outerPay_391
  · exact WuPaper.ClassicalFourthNat.outerPay_392
  · exact WuPaper.ClassicalFourthNat.outerPay_393
  · exact WuPaper.ClassicalFourthNat.outerPay_394
  · exact WuPaper.ClassicalFourthNat.outerPay_395
  · exact WuPaper.ClassicalFourthNat.outerPay_396
  · exact WuPaper.ClassicalFourthNat.outerPay_397
  · exact WuPaper.ClassicalFourthNat.outerPay_398
  · exact WuPaper.ClassicalFourthNat.outerPay_399
  · exact WuPaper.ClassicalFourthNat.outerPay_400
  · exact WuPaper.ClassicalFourthNat.outerPay_401
  · exact WuPaper.ClassicalFourthNat.outerPay_402
  · exact WuPaper.ClassicalFourthNat.outerPay_403
  · exact WuPaper.ClassicalFourthNat.outerPay_404
  · exact WuPaper.ClassicalFourthNat.outerPay_405
  · exact WuPaper.ClassicalFourthNat.outerPay_406
  · exact WuPaper.ClassicalFourthNat.outerPay_407
  · exact WuPaper.ClassicalFourthNat.outerPay_408
  · exact WuPaper.ClassicalFourthNat.outerPay_409
  · exact WuPaper.ClassicalFourthNat.outerPay_410
  · exact WuPaper.ClassicalFourthNat.outerPay_411
  · exact WuPaper.ClassicalFourthNat.outerPay_412
  · exact WuPaper.ClassicalFourthNat.outerPay_413
  · exact WuPaper.ClassicalFourthNat.outerPay_414
  · exact WuPaper.ClassicalFourthNat.outerPay_415
  · exact WuPaper.ClassicalFourthNat.outerPay_416
  · exact WuPaper.ClassicalFourthNat.outerPay_417
  · exact WuPaper.ClassicalFourthNat.outerPay_418
  · exact WuPaper.ClassicalFourthNat.outerPay_419
  · exact WuPaper.ClassicalFourthNat.outerPay_420
  · exact WuPaper.ClassicalFourthNat.outerPay_421
  · exact WuPaper.ClassicalFourthNat.outerPay_422
  · exact WuPaper.ClassicalFourthNat.outerPay_423
  · exact WuPaper.ClassicalFourthNat.outerPay_424
  · exact WuPaper.ClassicalFourthNat.outerPay_425
  · exact WuPaper.ClassicalFourthNat.outerPay_426
  · exact WuPaper.ClassicalFourthNat.outerPay_427
  · exact WuPaper.ClassicalFourthNat.outerPay_428
  · exact WuPaper.ClassicalFourthNat.outerPay_429
  · exact WuPaper.ClassicalFourthNat.outerPay_430
  · exact WuPaper.ClassicalFourthNat.outerPay_431
  · exact WuPaper.ClassicalFourthNat.outerPay_432
  · exact WuPaper.ClassicalFourthNat.outerPay_433
  · exact WuPaper.ClassicalFourthNat.outerPay_434
  · exact WuPaper.ClassicalFourthNat.outerPay_435
  · exact WuPaper.ClassicalFourthNat.outerPay_436
  · exact WuPaper.ClassicalFourthNat.outerPay_437
  · exact WuPaper.ClassicalFourthNat.outerPay_438
  · exact WuPaper.ClassicalFourthNat.outerPay_439
  · exact WuPaper.ClassicalFourthNat.outerPay_440
  · exact WuPaper.ClassicalFourthNat.outerPay_441
  · exact WuPaper.ClassicalFourthNat.outerPay_442
  · exact WuPaper.ClassicalFourthNat.outerPay_443
  · exact WuPaper.ClassicalFourthNat.outerPay_444
  · exact WuPaper.ClassicalFourthNat.outerPay_445
  · exact WuPaper.ClassicalFourthNat.outerPay_446
  · exact WuPaper.ClassicalFourthNat.outerPay_447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_006
