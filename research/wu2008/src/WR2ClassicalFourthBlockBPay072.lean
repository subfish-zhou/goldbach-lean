import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay072
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_072 (j : Fin 64) (hj : 64*72+j.val < 10540) :
    BPay (64*72+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4608
  · exact WuPaper.ClassicalFourthNat.BPay_4609
  · exact WuPaper.ClassicalFourthNat.BPay_4610
  · exact WuPaper.ClassicalFourthNat.BPay_4611
  · exact WuPaper.ClassicalFourthNat.BPay_4612
  · exact WuPaper.ClassicalFourthNat.BPay_4613
  · exact WuPaper.ClassicalFourthNat.BPay_4614
  · exact WuPaper.ClassicalFourthNat.BPay_4615
  · exact WuPaper.ClassicalFourthNat.BPay_4616
  · exact WuPaper.ClassicalFourthNat.BPay_4617
  · exact WuPaper.ClassicalFourthNat.BPay_4618
  · exact WuPaper.ClassicalFourthNat.BPay_4619
  · exact WuPaper.ClassicalFourthNat.BPay_4620
  · exact WuPaper.ClassicalFourthNat.BPay_4621
  · exact WuPaper.ClassicalFourthNat.BPay_4622
  · exact WuPaper.ClassicalFourthNat.BPay_4623
  · exact WuPaper.ClassicalFourthNat.BPay_4624
  · exact WuPaper.ClassicalFourthNat.BPay_4625
  · exact WuPaper.ClassicalFourthNat.BPay_4626
  · exact WuPaper.ClassicalFourthNat.BPay_4627
  · exact WuPaper.ClassicalFourthNat.BPay_4628
  · exact WuPaper.ClassicalFourthNat.BPay_4629
  · exact WuPaper.ClassicalFourthNat.BPay_4630
  · exact WuPaper.ClassicalFourthNat.BPay_4631
  · exact WuPaper.ClassicalFourthNat.BPay_4632
  · exact WuPaper.ClassicalFourthNat.BPay_4633
  · exact WuPaper.ClassicalFourthNat.BPay_4634
  · exact WuPaper.ClassicalFourthNat.BPay_4635
  · exact WuPaper.ClassicalFourthNat.BPay_4636
  · exact WuPaper.ClassicalFourthNat.BPay_4637
  · exact WuPaper.ClassicalFourthNat.BPay_4638
  · exact WuPaper.ClassicalFourthNat.BPay_4639
  · exact WuPaper.ClassicalFourthNat.BPay_4640
  · exact WuPaper.ClassicalFourthNat.BPay_4641
  · exact WuPaper.ClassicalFourthNat.BPay_4642
  · exact WuPaper.ClassicalFourthNat.BPay_4643
  · exact WuPaper.ClassicalFourthNat.BPay_4644
  · exact WuPaper.ClassicalFourthNat.BPay_4645
  · exact WuPaper.ClassicalFourthNat.BPay_4646
  · exact WuPaper.ClassicalFourthNat.BPay_4647
  · exact WuPaper.ClassicalFourthNat.BPay_4648
  · exact WuPaper.ClassicalFourthNat.BPay_4649
  · exact WuPaper.ClassicalFourthNat.BPay_4650
  · exact WuPaper.ClassicalFourthNat.BPay_4651
  · exact WuPaper.ClassicalFourthNat.BPay_4652
  · exact WuPaper.ClassicalFourthNat.BPay_4653
  · exact WuPaper.ClassicalFourthNat.BPay_4654
  · exact WuPaper.ClassicalFourthNat.BPay_4655
  · exact WuPaper.ClassicalFourthNat.BPay_4656
  · exact WuPaper.ClassicalFourthNat.BPay_4657
  · exact WuPaper.ClassicalFourthNat.BPay_4658
  · exact WuPaper.ClassicalFourthNat.BPay_4659
  · exact WuPaper.ClassicalFourthNat.BPay_4660
  · exact WuPaper.ClassicalFourthNat.BPay_4661
  · exact WuPaper.ClassicalFourthNat.BPay_4662
  · exact WuPaper.ClassicalFourthNat.BPay_4663
  · exact WuPaper.ClassicalFourthNat.BPay_4664
  · exact WuPaper.ClassicalFourthNat.BPay_4665
  · exact WuPaper.ClassicalFourthNat.BPay_4666
  · exact WuPaper.ClassicalFourthNat.BPay_4667
  · exact WuPaper.ClassicalFourthNat.BPay_4668
  · exact WuPaper.ClassicalFourthNat.BPay_4669
  · exact WuPaper.ClassicalFourthNat.BPay_4670
  · exact WuPaper.ClassicalFourthNat.BPay_4671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_072
