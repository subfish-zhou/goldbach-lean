import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay163
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_163 (j : Fin 64) (hj : 64*163+j.val < 10540) :
    OuterPay (64*163+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_10432
  · exact WuPaper.ClassicalFourthNat.outerPay_10433
  · exact WuPaper.ClassicalFourthNat.outerPay_10434
  · exact WuPaper.ClassicalFourthNat.outerPay_10435
  · exact WuPaper.ClassicalFourthNat.outerPay_10436
  · exact WuPaper.ClassicalFourthNat.outerPay_10437
  · exact WuPaper.ClassicalFourthNat.outerPay_10438
  · exact WuPaper.ClassicalFourthNat.outerPay_10439
  · exact WuPaper.ClassicalFourthNat.outerPay_10440
  · exact WuPaper.ClassicalFourthNat.outerPay_10441
  · exact WuPaper.ClassicalFourthNat.outerPay_10442
  · exact WuPaper.ClassicalFourthNat.outerPay_10443
  · exact WuPaper.ClassicalFourthNat.outerPay_10444
  · exact WuPaper.ClassicalFourthNat.outerPay_10445
  · exact WuPaper.ClassicalFourthNat.outerPay_10446
  · exact WuPaper.ClassicalFourthNat.outerPay_10447
  · exact WuPaper.ClassicalFourthNat.outerPay_10448
  · exact WuPaper.ClassicalFourthNat.outerPay_10449
  · exact WuPaper.ClassicalFourthNat.outerPay_10450
  · exact WuPaper.ClassicalFourthNat.outerPay_10451
  · exact WuPaper.ClassicalFourthNat.outerPay_10452
  · exact WuPaper.ClassicalFourthNat.outerPay_10453
  · exact WuPaper.ClassicalFourthNat.outerPay_10454
  · exact WuPaper.ClassicalFourthNat.outerPay_10455
  · exact WuPaper.ClassicalFourthNat.outerPay_10456
  · exact WuPaper.ClassicalFourthNat.outerPay_10457
  · exact WuPaper.ClassicalFourthNat.outerPay_10458
  · exact WuPaper.ClassicalFourthNat.outerPay_10459
  · exact WuPaper.ClassicalFourthNat.outerPay_10460
  · exact WuPaper.ClassicalFourthNat.outerPay_10461
  · exact WuPaper.ClassicalFourthNat.outerPay_10462
  · exact WuPaper.ClassicalFourthNat.outerPay_10463
  · exact WuPaper.ClassicalFourthNat.outerPay_10464
  · exact WuPaper.ClassicalFourthNat.outerPay_10465
  · exact WuPaper.ClassicalFourthNat.outerPay_10466
  · exact WuPaper.ClassicalFourthNat.outerPay_10467
  · exact WuPaper.ClassicalFourthNat.outerPay_10468
  · exact WuPaper.ClassicalFourthNat.outerPay_10469
  · exact WuPaper.ClassicalFourthNat.outerPay_10470
  · exact WuPaper.ClassicalFourthNat.outerPay_10471
  · exact WuPaper.ClassicalFourthNat.outerPay_10472
  · exact WuPaper.ClassicalFourthNat.outerPay_10473
  · exact WuPaper.ClassicalFourthNat.outerPay_10474
  · exact WuPaper.ClassicalFourthNat.outerPay_10475
  · exact WuPaper.ClassicalFourthNat.outerPay_10476
  · exact WuPaper.ClassicalFourthNat.outerPay_10477
  · exact WuPaper.ClassicalFourthNat.outerPay_10478
  · exact WuPaper.ClassicalFourthNat.outerPay_10479
  · exact WuPaper.ClassicalFourthNat.outerPay_10480
  · exact WuPaper.ClassicalFourthNat.outerPay_10481
  · exact WuPaper.ClassicalFourthNat.outerPay_10482
  · exact WuPaper.ClassicalFourthNat.outerPay_10483
  · exact WuPaper.ClassicalFourthNat.outerPay_10484
  · exact WuPaper.ClassicalFourthNat.outerPay_10485
  · exact WuPaper.ClassicalFourthNat.outerPay_10486
  · exact WuPaper.ClassicalFourthNat.outerPay_10487
  · exact WuPaper.ClassicalFourthNat.outerPay_10488
  · exact WuPaper.ClassicalFourthNat.outerPay_10489
  · exact WuPaper.ClassicalFourthNat.outerPay_10490
  · exact WuPaper.ClassicalFourthNat.outerPay_10491
  · exact WuPaper.ClassicalFourthNat.outerPay_10492
  · exact WuPaper.ClassicalFourthNat.outerPay_10493
  · exact WuPaper.ClassicalFourthNat.outerPay_10494
  · exact WuPaper.ClassicalFourthNat.outerPay_10495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_163
