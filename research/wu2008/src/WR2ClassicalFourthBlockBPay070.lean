import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay070
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_070 (j : Fin 64) (hj : 64*70+j.val < 10540) :
    BPay (64*70+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4480
  · exact WuPaper.ClassicalFourthNat.BPay_4481
  · exact WuPaper.ClassicalFourthNat.BPay_4482
  · exact WuPaper.ClassicalFourthNat.BPay_4483
  · exact WuPaper.ClassicalFourthNat.BPay_4484
  · exact WuPaper.ClassicalFourthNat.BPay_4485
  · exact WuPaper.ClassicalFourthNat.BPay_4486
  · exact WuPaper.ClassicalFourthNat.BPay_4487
  · exact WuPaper.ClassicalFourthNat.BPay_4488
  · exact WuPaper.ClassicalFourthNat.BPay_4489
  · exact WuPaper.ClassicalFourthNat.BPay_4490
  · exact WuPaper.ClassicalFourthNat.BPay_4491
  · exact WuPaper.ClassicalFourthNat.BPay_4492
  · exact WuPaper.ClassicalFourthNat.BPay_4493
  · exact WuPaper.ClassicalFourthNat.BPay_4494
  · exact WuPaper.ClassicalFourthNat.BPay_4495
  · exact WuPaper.ClassicalFourthNat.BPay_4496
  · exact WuPaper.ClassicalFourthNat.BPay_4497
  · exact WuPaper.ClassicalFourthNat.BPay_4498
  · exact WuPaper.ClassicalFourthNat.BPay_4499
  · exact WuPaper.ClassicalFourthNat.BPay_4500
  · exact WuPaper.ClassicalFourthNat.BPay_4501
  · exact WuPaper.ClassicalFourthNat.BPay_4502
  · exact WuPaper.ClassicalFourthNat.BPay_4503
  · exact WuPaper.ClassicalFourthNat.BPay_4504
  · exact WuPaper.ClassicalFourthNat.BPay_4505
  · exact WuPaper.ClassicalFourthNat.BPay_4506
  · exact WuPaper.ClassicalFourthNat.BPay_4507
  · exact WuPaper.ClassicalFourthNat.BPay_4508
  · exact WuPaper.ClassicalFourthNat.BPay_4509
  · exact WuPaper.ClassicalFourthNat.BPay_4510
  · exact WuPaper.ClassicalFourthNat.BPay_4511
  · exact WuPaper.ClassicalFourthNat.BPay_4512
  · exact WuPaper.ClassicalFourthNat.BPay_4513
  · exact WuPaper.ClassicalFourthNat.BPay_4514
  · exact WuPaper.ClassicalFourthNat.BPay_4515
  · exact WuPaper.ClassicalFourthNat.BPay_4516
  · exact WuPaper.ClassicalFourthNat.BPay_4517
  · exact WuPaper.ClassicalFourthNat.BPay_4518
  · exact WuPaper.ClassicalFourthNat.BPay_4519
  · exact WuPaper.ClassicalFourthNat.BPay_4520
  · exact WuPaper.ClassicalFourthNat.BPay_4521
  · exact WuPaper.ClassicalFourthNat.BPay_4522
  · exact WuPaper.ClassicalFourthNat.BPay_4523
  · exact WuPaper.ClassicalFourthNat.BPay_4524
  · exact WuPaper.ClassicalFourthNat.BPay_4525
  · exact WuPaper.ClassicalFourthNat.BPay_4526
  · exact WuPaper.ClassicalFourthNat.BPay_4527
  · exact WuPaper.ClassicalFourthNat.BPay_4528
  · exact WuPaper.ClassicalFourthNat.BPay_4529
  · exact WuPaper.ClassicalFourthNat.BPay_4530
  · exact WuPaper.ClassicalFourthNat.BPay_4531
  · exact WuPaper.ClassicalFourthNat.BPay_4532
  · exact WuPaper.ClassicalFourthNat.BPay_4533
  · exact WuPaper.ClassicalFourthNat.BPay_4534
  · exact WuPaper.ClassicalFourthNat.BPay_4535
  · exact WuPaper.ClassicalFourthNat.BPay_4536
  · exact WuPaper.ClassicalFourthNat.BPay_4537
  · exact WuPaper.ClassicalFourthNat.BPay_4538
  · exact WuPaper.ClassicalFourthNat.BPay_4539
  · exact WuPaper.ClassicalFourthNat.BPay_4540
  · exact WuPaper.ClassicalFourthNat.BPay_4541
  · exact WuPaper.ClassicalFourthNat.BPay_4542
  · exact WuPaper.ClassicalFourthNat.BPay_4543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_070
