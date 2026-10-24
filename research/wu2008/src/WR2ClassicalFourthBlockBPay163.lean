import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay163
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_163 (j : Fin 64) (hj : 64*163+j.val < 10540) :
    BPay (64*163+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10432
  · exact WuPaper.ClassicalFourthNat.BPay_10433
  · exact WuPaper.ClassicalFourthNat.BPay_10434
  · exact WuPaper.ClassicalFourthNat.BPay_10435
  · exact WuPaper.ClassicalFourthNat.BPay_10436
  · exact WuPaper.ClassicalFourthNat.BPay_10437
  · exact WuPaper.ClassicalFourthNat.BPay_10438
  · exact WuPaper.ClassicalFourthNat.BPay_10439
  · exact WuPaper.ClassicalFourthNat.BPay_10440
  · exact WuPaper.ClassicalFourthNat.BPay_10441
  · exact WuPaper.ClassicalFourthNat.BPay_10442
  · exact WuPaper.ClassicalFourthNat.BPay_10443
  · exact WuPaper.ClassicalFourthNat.BPay_10444
  · exact WuPaper.ClassicalFourthNat.BPay_10445
  · exact WuPaper.ClassicalFourthNat.BPay_10446
  · exact WuPaper.ClassicalFourthNat.BPay_10447
  · exact WuPaper.ClassicalFourthNat.BPay_10448
  · exact WuPaper.ClassicalFourthNat.BPay_10449
  · exact WuPaper.ClassicalFourthNat.BPay_10450
  · exact WuPaper.ClassicalFourthNat.BPay_10451
  · exact WuPaper.ClassicalFourthNat.BPay_10452
  · exact WuPaper.ClassicalFourthNat.BPay_10453
  · exact WuPaper.ClassicalFourthNat.BPay_10454
  · exact WuPaper.ClassicalFourthNat.BPay_10455
  · exact WuPaper.ClassicalFourthNat.BPay_10456
  · exact WuPaper.ClassicalFourthNat.BPay_10457
  · exact WuPaper.ClassicalFourthNat.BPay_10458
  · exact WuPaper.ClassicalFourthNat.BPay_10459
  · exact WuPaper.ClassicalFourthNat.BPay_10460
  · exact WuPaper.ClassicalFourthNat.BPay_10461
  · exact WuPaper.ClassicalFourthNat.BPay_10462
  · exact WuPaper.ClassicalFourthNat.BPay_10463
  · exact WuPaper.ClassicalFourthNat.BPay_10464
  · exact WuPaper.ClassicalFourthNat.BPay_10465
  · exact WuPaper.ClassicalFourthNat.BPay_10466
  · exact WuPaper.ClassicalFourthNat.BPay_10467
  · exact WuPaper.ClassicalFourthNat.BPay_10468
  · exact WuPaper.ClassicalFourthNat.BPay_10469
  · exact WuPaper.ClassicalFourthNat.BPay_10470
  · exact WuPaper.ClassicalFourthNat.BPay_10471
  · exact WuPaper.ClassicalFourthNat.BPay_10472
  · exact WuPaper.ClassicalFourthNat.BPay_10473
  · exact WuPaper.ClassicalFourthNat.BPay_10474
  · exact WuPaper.ClassicalFourthNat.BPay_10475
  · exact WuPaper.ClassicalFourthNat.BPay_10476
  · exact WuPaper.ClassicalFourthNat.BPay_10477
  · exact WuPaper.ClassicalFourthNat.BPay_10478
  · exact WuPaper.ClassicalFourthNat.BPay_10479
  · exact WuPaper.ClassicalFourthNat.BPay_10480
  · exact WuPaper.ClassicalFourthNat.BPay_10481
  · exact WuPaper.ClassicalFourthNat.BPay_10482
  · exact WuPaper.ClassicalFourthNat.BPay_10483
  · exact WuPaper.ClassicalFourthNat.BPay_10484
  · exact WuPaper.ClassicalFourthNat.BPay_10485
  · exact WuPaper.ClassicalFourthNat.BPay_10486
  · exact WuPaper.ClassicalFourthNat.BPay_10487
  · exact WuPaper.ClassicalFourthNat.BPay_10488
  · exact WuPaper.ClassicalFourthNat.BPay_10489
  · exact WuPaper.ClassicalFourthNat.BPay_10490
  · exact WuPaper.ClassicalFourthNat.BPay_10491
  · exact WuPaper.ClassicalFourthNat.BPay_10492
  · exact WuPaper.ClassicalFourthNat.BPay_10493
  · exact WuPaper.ClassicalFourthNat.BPay_10494
  · exact WuPaper.ClassicalFourthNat.BPay_10495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_163
