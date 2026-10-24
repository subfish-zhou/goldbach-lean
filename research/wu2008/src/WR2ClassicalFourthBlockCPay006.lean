import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay006
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_006 (j : Fin 64) (hj : 64*6+j.val < 2540) :
    CPay (64*6+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_384
  · exact WuPaper.ClassicalFourthNat.CPay_385
  · exact WuPaper.ClassicalFourthNat.CPay_386
  · exact WuPaper.ClassicalFourthNat.CPay_387
  · exact WuPaper.ClassicalFourthNat.CPay_388
  · exact WuPaper.ClassicalFourthNat.CPay_389
  · exact WuPaper.ClassicalFourthNat.CPay_390
  · exact WuPaper.ClassicalFourthNat.CPay_391
  · exact WuPaper.ClassicalFourthNat.CPay_392
  · exact WuPaper.ClassicalFourthNat.CPay_393
  · exact WuPaper.ClassicalFourthNat.CPay_394
  · exact WuPaper.ClassicalFourthNat.CPay_395
  · exact WuPaper.ClassicalFourthNat.CPay_396
  · exact WuPaper.ClassicalFourthNat.CPay_397
  · exact WuPaper.ClassicalFourthNat.CPay_398
  · exact WuPaper.ClassicalFourthNat.CPay_399
  · exact WuPaper.ClassicalFourthNat.CPay_400
  · exact WuPaper.ClassicalFourthNat.CPay_401
  · exact WuPaper.ClassicalFourthNat.CPay_402
  · exact WuPaper.ClassicalFourthNat.CPay_403
  · exact WuPaper.ClassicalFourthNat.CPay_404
  · exact WuPaper.ClassicalFourthNat.CPay_405
  · exact WuPaper.ClassicalFourthNat.CPay_406
  · exact WuPaper.ClassicalFourthNat.CPay_407
  · exact WuPaper.ClassicalFourthNat.CPay_408
  · exact WuPaper.ClassicalFourthNat.CPay_409
  · exact WuPaper.ClassicalFourthNat.CPay_410
  · exact WuPaper.ClassicalFourthNat.CPay_411
  · exact WuPaper.ClassicalFourthNat.CPay_412
  · exact WuPaper.ClassicalFourthNat.CPay_413
  · exact WuPaper.ClassicalFourthNat.CPay_414
  · exact WuPaper.ClassicalFourthNat.CPay_415
  · exact WuPaper.ClassicalFourthNat.CPay_416
  · exact WuPaper.ClassicalFourthNat.CPay_417
  · exact WuPaper.ClassicalFourthNat.CPay_418
  · exact WuPaper.ClassicalFourthNat.CPay_419
  · exact WuPaper.ClassicalFourthNat.CPay_420
  · exact WuPaper.ClassicalFourthNat.CPay_421
  · exact WuPaper.ClassicalFourthNat.CPay_422
  · exact WuPaper.ClassicalFourthNat.CPay_423
  · exact WuPaper.ClassicalFourthNat.CPay_424
  · exact WuPaper.ClassicalFourthNat.CPay_425
  · exact WuPaper.ClassicalFourthNat.CPay_426
  · exact WuPaper.ClassicalFourthNat.CPay_427
  · exact WuPaper.ClassicalFourthNat.CPay_428
  · exact WuPaper.ClassicalFourthNat.CPay_429
  · exact WuPaper.ClassicalFourthNat.CPay_430
  · exact WuPaper.ClassicalFourthNat.CPay_431
  · exact WuPaper.ClassicalFourthNat.CPay_432
  · exact WuPaper.ClassicalFourthNat.CPay_433
  · exact WuPaper.ClassicalFourthNat.CPay_434
  · exact WuPaper.ClassicalFourthNat.CPay_435
  · exact WuPaper.ClassicalFourthNat.CPay_436
  · exact WuPaper.ClassicalFourthNat.CPay_437
  · exact WuPaper.ClassicalFourthNat.CPay_438
  · exact WuPaper.ClassicalFourthNat.CPay_439
  · exact WuPaper.ClassicalFourthNat.CPay_440
  · exact WuPaper.ClassicalFourthNat.CPay_441
  · exact WuPaper.ClassicalFourthNat.CPay_442
  · exact WuPaper.ClassicalFourthNat.CPay_443
  · exact WuPaper.ClassicalFourthNat.CPay_444
  · exact WuPaper.ClassicalFourthNat.CPay_445
  · exact WuPaper.ClassicalFourthNat.CPay_446
  · exact WuPaper.ClassicalFourthNat.CPay_447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_006
