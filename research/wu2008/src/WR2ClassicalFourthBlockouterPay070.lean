import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay070
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_070 (j : Fin 64) (hj : 64*70+j.val < 10540) :
    OuterPay (64*70+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_4480
  · exact WuPaper.ClassicalFourthNat.outerPay_4481
  · exact WuPaper.ClassicalFourthNat.outerPay_4482
  · exact WuPaper.ClassicalFourthNat.outerPay_4483
  · exact WuPaper.ClassicalFourthNat.outerPay_4484
  · exact WuPaper.ClassicalFourthNat.outerPay_4485
  · exact WuPaper.ClassicalFourthNat.outerPay_4486
  · exact WuPaper.ClassicalFourthNat.outerPay_4487
  · exact WuPaper.ClassicalFourthNat.outerPay_4488
  · exact WuPaper.ClassicalFourthNat.outerPay_4489
  · exact WuPaper.ClassicalFourthNat.outerPay_4490
  · exact WuPaper.ClassicalFourthNat.outerPay_4491
  · exact WuPaper.ClassicalFourthNat.outerPay_4492
  · exact WuPaper.ClassicalFourthNat.outerPay_4493
  · exact WuPaper.ClassicalFourthNat.outerPay_4494
  · exact WuPaper.ClassicalFourthNat.outerPay_4495
  · exact WuPaper.ClassicalFourthNat.outerPay_4496
  · exact WuPaper.ClassicalFourthNat.outerPay_4497
  · exact WuPaper.ClassicalFourthNat.outerPay_4498
  · exact WuPaper.ClassicalFourthNat.outerPay_4499
  · exact WuPaper.ClassicalFourthNat.outerPay_4500
  · exact WuPaper.ClassicalFourthNat.outerPay_4501
  · exact WuPaper.ClassicalFourthNat.outerPay_4502
  · exact WuPaper.ClassicalFourthNat.outerPay_4503
  · exact WuPaper.ClassicalFourthNat.outerPay_4504
  · exact WuPaper.ClassicalFourthNat.outerPay_4505
  · exact WuPaper.ClassicalFourthNat.outerPay_4506
  · exact WuPaper.ClassicalFourthNat.outerPay_4507
  · exact WuPaper.ClassicalFourthNat.outerPay_4508
  · exact WuPaper.ClassicalFourthNat.outerPay_4509
  · exact WuPaper.ClassicalFourthNat.outerPay_4510
  · exact WuPaper.ClassicalFourthNat.outerPay_4511
  · exact WuPaper.ClassicalFourthNat.outerPay_4512
  · exact WuPaper.ClassicalFourthNat.outerPay_4513
  · exact WuPaper.ClassicalFourthNat.outerPay_4514
  · exact WuPaper.ClassicalFourthNat.outerPay_4515
  · exact WuPaper.ClassicalFourthNat.outerPay_4516
  · exact WuPaper.ClassicalFourthNat.outerPay_4517
  · exact WuPaper.ClassicalFourthNat.outerPay_4518
  · exact WuPaper.ClassicalFourthNat.outerPay_4519
  · exact WuPaper.ClassicalFourthNat.outerPay_4520
  · exact WuPaper.ClassicalFourthNat.outerPay_4521
  · exact WuPaper.ClassicalFourthNat.outerPay_4522
  · exact WuPaper.ClassicalFourthNat.outerPay_4523
  · exact WuPaper.ClassicalFourthNat.outerPay_4524
  · exact WuPaper.ClassicalFourthNat.outerPay_4525
  · exact WuPaper.ClassicalFourthNat.outerPay_4526
  · exact WuPaper.ClassicalFourthNat.outerPay_4527
  · exact WuPaper.ClassicalFourthNat.outerPay_4528
  · exact WuPaper.ClassicalFourthNat.outerPay_4529
  · exact WuPaper.ClassicalFourthNat.outerPay_4530
  · exact WuPaper.ClassicalFourthNat.outerPay_4531
  · exact WuPaper.ClassicalFourthNat.outerPay_4532
  · exact WuPaper.ClassicalFourthNat.outerPay_4533
  · exact WuPaper.ClassicalFourthNat.outerPay_4534
  · exact WuPaper.ClassicalFourthNat.outerPay_4535
  · exact WuPaper.ClassicalFourthNat.outerPay_4536
  · exact WuPaper.ClassicalFourthNat.outerPay_4537
  · exact WuPaper.ClassicalFourthNat.outerPay_4538
  · exact WuPaper.ClassicalFourthNat.outerPay_4539
  · exact WuPaper.ClassicalFourthNat.outerPay_4540
  · exact WuPaper.ClassicalFourthNat.outerPay_4541
  · exact WuPaper.ClassicalFourthNat.outerPay_4542
  · exact WuPaper.ClassicalFourthNat.outerPay_4543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_070
