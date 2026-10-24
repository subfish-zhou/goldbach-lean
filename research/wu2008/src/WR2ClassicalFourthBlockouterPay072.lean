import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay072
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_072 (j : Fin 64) (hj : 64*72+j.val < 10540) :
    OuterPay (64*72+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_4608
  · exact WuPaper.ClassicalFourthNat.outerPay_4609
  · exact WuPaper.ClassicalFourthNat.outerPay_4610
  · exact WuPaper.ClassicalFourthNat.outerPay_4611
  · exact WuPaper.ClassicalFourthNat.outerPay_4612
  · exact WuPaper.ClassicalFourthNat.outerPay_4613
  · exact WuPaper.ClassicalFourthNat.outerPay_4614
  · exact WuPaper.ClassicalFourthNat.outerPay_4615
  · exact WuPaper.ClassicalFourthNat.outerPay_4616
  · exact WuPaper.ClassicalFourthNat.outerPay_4617
  · exact WuPaper.ClassicalFourthNat.outerPay_4618
  · exact WuPaper.ClassicalFourthNat.outerPay_4619
  · exact WuPaper.ClassicalFourthNat.outerPay_4620
  · exact WuPaper.ClassicalFourthNat.outerPay_4621
  · exact WuPaper.ClassicalFourthNat.outerPay_4622
  · exact WuPaper.ClassicalFourthNat.outerPay_4623
  · exact WuPaper.ClassicalFourthNat.outerPay_4624
  · exact WuPaper.ClassicalFourthNat.outerPay_4625
  · exact WuPaper.ClassicalFourthNat.outerPay_4626
  · exact WuPaper.ClassicalFourthNat.outerPay_4627
  · exact WuPaper.ClassicalFourthNat.outerPay_4628
  · exact WuPaper.ClassicalFourthNat.outerPay_4629
  · exact WuPaper.ClassicalFourthNat.outerPay_4630
  · exact WuPaper.ClassicalFourthNat.outerPay_4631
  · exact WuPaper.ClassicalFourthNat.outerPay_4632
  · exact WuPaper.ClassicalFourthNat.outerPay_4633
  · exact WuPaper.ClassicalFourthNat.outerPay_4634
  · exact WuPaper.ClassicalFourthNat.outerPay_4635
  · exact WuPaper.ClassicalFourthNat.outerPay_4636
  · exact WuPaper.ClassicalFourthNat.outerPay_4637
  · exact WuPaper.ClassicalFourthNat.outerPay_4638
  · exact WuPaper.ClassicalFourthNat.outerPay_4639
  · exact WuPaper.ClassicalFourthNat.outerPay_4640
  · exact WuPaper.ClassicalFourthNat.outerPay_4641
  · exact WuPaper.ClassicalFourthNat.outerPay_4642
  · exact WuPaper.ClassicalFourthNat.outerPay_4643
  · exact WuPaper.ClassicalFourthNat.outerPay_4644
  · exact WuPaper.ClassicalFourthNat.outerPay_4645
  · exact WuPaper.ClassicalFourthNat.outerPay_4646
  · exact WuPaper.ClassicalFourthNat.outerPay_4647
  · exact WuPaper.ClassicalFourthNat.outerPay_4648
  · exact WuPaper.ClassicalFourthNat.outerPay_4649
  · exact WuPaper.ClassicalFourthNat.outerPay_4650
  · exact WuPaper.ClassicalFourthNat.outerPay_4651
  · exact WuPaper.ClassicalFourthNat.outerPay_4652
  · exact WuPaper.ClassicalFourthNat.outerPay_4653
  · exact WuPaper.ClassicalFourthNat.outerPay_4654
  · exact WuPaper.ClassicalFourthNat.outerPay_4655
  · exact WuPaper.ClassicalFourthNat.outerPay_4656
  · exact WuPaper.ClassicalFourthNat.outerPay_4657
  · exact WuPaper.ClassicalFourthNat.outerPay_4658
  · exact WuPaper.ClassicalFourthNat.outerPay_4659
  · exact WuPaper.ClassicalFourthNat.outerPay_4660
  · exact WuPaper.ClassicalFourthNat.outerPay_4661
  · exact WuPaper.ClassicalFourthNat.outerPay_4662
  · exact WuPaper.ClassicalFourthNat.outerPay_4663
  · exact WuPaper.ClassicalFourthNat.outerPay_4664
  · exact WuPaper.ClassicalFourthNat.outerPay_4665
  · exact WuPaper.ClassicalFourthNat.outerPay_4666
  · exact WuPaper.ClassicalFourthNat.outerPay_4667
  · exact WuPaper.ClassicalFourthNat.outerPay_4668
  · exact WuPaper.ClassicalFourthNat.outerPay_4669
  · exact WuPaper.ClassicalFourthNat.outerPay_4670
  · exact WuPaper.ClassicalFourthNat.outerPay_4671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_072
