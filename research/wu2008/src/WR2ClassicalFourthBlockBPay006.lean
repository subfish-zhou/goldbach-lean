import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay006
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_006 (j : Fin 64) (hj : 64*6+j.val < 10540) :
    BPay (64*6+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_384
  · exact WuPaper.ClassicalFourthNat.BPay_385
  · exact WuPaper.ClassicalFourthNat.BPay_386
  · exact WuPaper.ClassicalFourthNat.BPay_387
  · exact WuPaper.ClassicalFourthNat.BPay_388
  · exact WuPaper.ClassicalFourthNat.BPay_389
  · exact WuPaper.ClassicalFourthNat.BPay_390
  · exact WuPaper.ClassicalFourthNat.BPay_391
  · exact WuPaper.ClassicalFourthNat.BPay_392
  · exact WuPaper.ClassicalFourthNat.BPay_393
  · exact WuPaper.ClassicalFourthNat.BPay_394
  · exact WuPaper.ClassicalFourthNat.BPay_395
  · exact WuPaper.ClassicalFourthNat.BPay_396
  · exact WuPaper.ClassicalFourthNat.BPay_397
  · exact WuPaper.ClassicalFourthNat.BPay_398
  · exact WuPaper.ClassicalFourthNat.BPay_399
  · exact WuPaper.ClassicalFourthNat.BPay_400
  · exact WuPaper.ClassicalFourthNat.BPay_401
  · exact WuPaper.ClassicalFourthNat.BPay_402
  · exact WuPaper.ClassicalFourthNat.BPay_403
  · exact WuPaper.ClassicalFourthNat.BPay_404
  · exact WuPaper.ClassicalFourthNat.BPay_405
  · exact WuPaper.ClassicalFourthNat.BPay_406
  · exact WuPaper.ClassicalFourthNat.BPay_407
  · exact WuPaper.ClassicalFourthNat.BPay_408
  · exact WuPaper.ClassicalFourthNat.BPay_409
  · exact WuPaper.ClassicalFourthNat.BPay_410
  · exact WuPaper.ClassicalFourthNat.BPay_411
  · exact WuPaper.ClassicalFourthNat.BPay_412
  · exact WuPaper.ClassicalFourthNat.BPay_413
  · exact WuPaper.ClassicalFourthNat.BPay_414
  · exact WuPaper.ClassicalFourthNat.BPay_415
  · exact WuPaper.ClassicalFourthNat.BPay_416
  · exact WuPaper.ClassicalFourthNat.BPay_417
  · exact WuPaper.ClassicalFourthNat.BPay_418
  · exact WuPaper.ClassicalFourthNat.BPay_419
  · exact WuPaper.ClassicalFourthNat.BPay_420
  · exact WuPaper.ClassicalFourthNat.BPay_421
  · exact WuPaper.ClassicalFourthNat.BPay_422
  · exact WuPaper.ClassicalFourthNat.BPay_423
  · exact WuPaper.ClassicalFourthNat.BPay_424
  · exact WuPaper.ClassicalFourthNat.BPay_425
  · exact WuPaper.ClassicalFourthNat.BPay_426
  · exact WuPaper.ClassicalFourthNat.BPay_427
  · exact WuPaper.ClassicalFourthNat.BPay_428
  · exact WuPaper.ClassicalFourthNat.BPay_429
  · exact WuPaper.ClassicalFourthNat.BPay_430
  · exact WuPaper.ClassicalFourthNat.BPay_431
  · exact WuPaper.ClassicalFourthNat.BPay_432
  · exact WuPaper.ClassicalFourthNat.BPay_433
  · exact WuPaper.ClassicalFourthNat.BPay_434
  · exact WuPaper.ClassicalFourthNat.BPay_435
  · exact WuPaper.ClassicalFourthNat.BPay_436
  · exact WuPaper.ClassicalFourthNat.BPay_437
  · exact WuPaper.ClassicalFourthNat.BPay_438
  · exact WuPaper.ClassicalFourthNat.BPay_439
  · exact WuPaper.ClassicalFourthNat.BPay_440
  · exact WuPaper.ClassicalFourthNat.BPay_441
  · exact WuPaper.ClassicalFourthNat.BPay_442
  · exact WuPaper.ClassicalFourthNat.BPay_443
  · exact WuPaper.ClassicalFourthNat.BPay_444
  · exact WuPaper.ClassicalFourthNat.BPay_445
  · exact WuPaper.ClassicalFourthNat.BPay_446
  · exact WuPaper.ClassicalFourthNat.BPay_447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_006
