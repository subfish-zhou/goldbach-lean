import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay071
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_071 (j : Fin 64) (hj : 64*71+j.val < 10540) :
    BPay (64*71+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4544
  · exact WuPaper.ClassicalFourthNat.BPay_4545
  · exact WuPaper.ClassicalFourthNat.BPay_4546
  · exact WuPaper.ClassicalFourthNat.BPay_4547
  · exact WuPaper.ClassicalFourthNat.BPay_4548
  · exact WuPaper.ClassicalFourthNat.BPay_4549
  · exact WuPaper.ClassicalFourthNat.BPay_4550
  · exact WuPaper.ClassicalFourthNat.BPay_4551
  · exact WuPaper.ClassicalFourthNat.BPay_4552
  · exact WuPaper.ClassicalFourthNat.BPay_4553
  · exact WuPaper.ClassicalFourthNat.BPay_4554
  · exact WuPaper.ClassicalFourthNat.BPay_4555
  · exact WuPaper.ClassicalFourthNat.BPay_4556
  · exact WuPaper.ClassicalFourthNat.BPay_4557
  · exact WuPaper.ClassicalFourthNat.BPay_4558
  · exact WuPaper.ClassicalFourthNat.BPay_4559
  · exact WuPaper.ClassicalFourthNat.BPay_4560
  · exact WuPaper.ClassicalFourthNat.BPay_4561
  · exact WuPaper.ClassicalFourthNat.BPay_4562
  · exact WuPaper.ClassicalFourthNat.BPay_4563
  · exact WuPaper.ClassicalFourthNat.BPay_4564
  · exact WuPaper.ClassicalFourthNat.BPay_4565
  · exact WuPaper.ClassicalFourthNat.BPay_4566
  · exact WuPaper.ClassicalFourthNat.BPay_4567
  · exact WuPaper.ClassicalFourthNat.BPay_4568
  · exact WuPaper.ClassicalFourthNat.BPay_4569
  · exact WuPaper.ClassicalFourthNat.BPay_4570
  · exact WuPaper.ClassicalFourthNat.BPay_4571
  · exact WuPaper.ClassicalFourthNat.BPay_4572
  · exact WuPaper.ClassicalFourthNat.BPay_4573
  · exact WuPaper.ClassicalFourthNat.BPay_4574
  · exact WuPaper.ClassicalFourthNat.BPay_4575
  · exact WuPaper.ClassicalFourthNat.BPay_4576
  · exact WuPaper.ClassicalFourthNat.BPay_4577
  · exact WuPaper.ClassicalFourthNat.BPay_4578
  · exact WuPaper.ClassicalFourthNat.BPay_4579
  · exact WuPaper.ClassicalFourthNat.BPay_4580
  · exact WuPaper.ClassicalFourthNat.BPay_4581
  · exact WuPaper.ClassicalFourthNat.BPay_4582
  · exact WuPaper.ClassicalFourthNat.BPay_4583
  · exact WuPaper.ClassicalFourthNat.BPay_4584
  · exact WuPaper.ClassicalFourthNat.BPay_4585
  · exact WuPaper.ClassicalFourthNat.BPay_4586
  · exact WuPaper.ClassicalFourthNat.BPay_4587
  · exact WuPaper.ClassicalFourthNat.BPay_4588
  · exact WuPaper.ClassicalFourthNat.BPay_4589
  · exact WuPaper.ClassicalFourthNat.BPay_4590
  · exact WuPaper.ClassicalFourthNat.BPay_4591
  · exact WuPaper.ClassicalFourthNat.BPay_4592
  · exact WuPaper.ClassicalFourthNat.BPay_4593
  · exact WuPaper.ClassicalFourthNat.BPay_4594
  · exact WuPaper.ClassicalFourthNat.BPay_4595
  · exact WuPaper.ClassicalFourthNat.BPay_4596
  · exact WuPaper.ClassicalFourthNat.BPay_4597
  · exact WuPaper.ClassicalFourthNat.BPay_4598
  · exact WuPaper.ClassicalFourthNat.BPay_4599
  · exact WuPaper.ClassicalFourthNat.BPay_4600
  · exact WuPaper.ClassicalFourthNat.BPay_4601
  · exact WuPaper.ClassicalFourthNat.BPay_4602
  · exact WuPaper.ClassicalFourthNat.BPay_4603
  · exact WuPaper.ClassicalFourthNat.BPay_4604
  · exact WuPaper.ClassicalFourthNat.BPay_4605
  · exact WuPaper.ClassicalFourthNat.BPay_4606
  · exact WuPaper.ClassicalFourthNat.BPay_4607
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_071
