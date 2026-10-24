import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint006
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_006 (j : Fin 64) (hj : 64*6+j.val < 10541) :
    OuterPoint (64*6+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_384
  · exact WuPaper.ClassicalFourthNat.OuterPoint_385
  · exact WuPaper.ClassicalFourthNat.OuterPoint_386
  · exact WuPaper.ClassicalFourthNat.OuterPoint_387
  · exact WuPaper.ClassicalFourthNat.OuterPoint_388
  · exact WuPaper.ClassicalFourthNat.OuterPoint_389
  · exact WuPaper.ClassicalFourthNat.OuterPoint_390
  · exact WuPaper.ClassicalFourthNat.OuterPoint_391
  · exact WuPaper.ClassicalFourthNat.OuterPoint_392
  · exact WuPaper.ClassicalFourthNat.OuterPoint_393
  · exact WuPaper.ClassicalFourthNat.OuterPoint_394
  · exact WuPaper.ClassicalFourthNat.OuterPoint_395
  · exact WuPaper.ClassicalFourthNat.OuterPoint_396
  · exact WuPaper.ClassicalFourthNat.OuterPoint_397
  · exact WuPaper.ClassicalFourthNat.OuterPoint_398
  · exact WuPaper.ClassicalFourthNat.OuterPoint_399
  · exact WuPaper.ClassicalFourthNat.OuterPoint_400
  · exact WuPaper.ClassicalFourthNat.OuterPoint_401
  · exact WuPaper.ClassicalFourthNat.OuterPoint_402
  · exact WuPaper.ClassicalFourthNat.OuterPoint_403
  · exact WuPaper.ClassicalFourthNat.OuterPoint_404
  · exact WuPaper.ClassicalFourthNat.OuterPoint_405
  · exact WuPaper.ClassicalFourthNat.OuterPoint_406
  · exact WuPaper.ClassicalFourthNat.OuterPoint_407
  · exact WuPaper.ClassicalFourthNat.OuterPoint_408
  · exact WuPaper.ClassicalFourthNat.OuterPoint_409
  · exact WuPaper.ClassicalFourthNat.OuterPoint_410
  · exact WuPaper.ClassicalFourthNat.OuterPoint_411
  · exact WuPaper.ClassicalFourthNat.OuterPoint_412
  · exact WuPaper.ClassicalFourthNat.OuterPoint_413
  · exact WuPaper.ClassicalFourthNat.OuterPoint_414
  · exact WuPaper.ClassicalFourthNat.OuterPoint_415
  · exact WuPaper.ClassicalFourthNat.OuterPoint_416
  · exact WuPaper.ClassicalFourthNat.OuterPoint_417
  · exact WuPaper.ClassicalFourthNat.OuterPoint_418
  · exact WuPaper.ClassicalFourthNat.OuterPoint_419
  · exact WuPaper.ClassicalFourthNat.OuterPoint_420
  · exact WuPaper.ClassicalFourthNat.OuterPoint_421
  · exact WuPaper.ClassicalFourthNat.OuterPoint_422
  · exact WuPaper.ClassicalFourthNat.OuterPoint_423
  · exact WuPaper.ClassicalFourthNat.OuterPoint_424
  · exact WuPaper.ClassicalFourthNat.OuterPoint_425
  · exact WuPaper.ClassicalFourthNat.OuterPoint_426
  · exact WuPaper.ClassicalFourthNat.OuterPoint_427
  · exact WuPaper.ClassicalFourthNat.OuterPoint_428
  · exact WuPaper.ClassicalFourthNat.OuterPoint_429
  · exact WuPaper.ClassicalFourthNat.OuterPoint_430
  · exact WuPaper.ClassicalFourthNat.OuterPoint_431
  · exact WuPaper.ClassicalFourthNat.OuterPoint_432
  · exact WuPaper.ClassicalFourthNat.OuterPoint_433
  · exact WuPaper.ClassicalFourthNat.OuterPoint_434
  · exact WuPaper.ClassicalFourthNat.OuterPoint_435
  · exact WuPaper.ClassicalFourthNat.OuterPoint_436
  · exact WuPaper.ClassicalFourthNat.OuterPoint_437
  · exact WuPaper.ClassicalFourthNat.OuterPoint_438
  · exact WuPaper.ClassicalFourthNat.OuterPoint_439
  · exact WuPaper.ClassicalFourthNat.OuterPoint_440
  · exact WuPaper.ClassicalFourthNat.OuterPoint_441
  · exact WuPaper.ClassicalFourthNat.OuterPoint_442
  · exact WuPaper.ClassicalFourthNat.OuterPoint_443
  · exact WuPaper.ClassicalFourthNat.OuterPoint_444
  · exact WuPaper.ClassicalFourthNat.OuterPoint_445
  · exact WuPaper.ClassicalFourthNat.OuterPoint_446
  · exact WuPaper.ClassicalFourthNat.OuterPoint_447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_006
