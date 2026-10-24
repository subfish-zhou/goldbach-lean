import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint163
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_163 (j : Fin 64) (hj : 64*163+j.val < 10541) :
    OuterPoint (64*163+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10432
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10433
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10434
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10435
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10436
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10437
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10438
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10439
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10440
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10441
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10442
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10443
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10444
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10445
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10446
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10447
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10448
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10449
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10450
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10451
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10452
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10453
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10454
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10455
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10456
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10457
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10458
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10459
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10460
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10461
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10462
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10463
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10464
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10465
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10466
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10467
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10468
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10469
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10470
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10471
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10472
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10473
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10474
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10475
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10476
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10477
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10478
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10479
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10480
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10481
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10482
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10483
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10484
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10485
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10486
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10487
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10488
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10489
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10490
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10491
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10492
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10493
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10494
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_163
