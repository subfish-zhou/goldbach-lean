import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay073
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_073 (j : Fin 64) (hj : 64*73+j.val < 10540) :
    BPay (64*73+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4672
  · exact WuPaper.ClassicalFourthNat.BPay_4673
  · exact WuPaper.ClassicalFourthNat.BPay_4674
  · exact WuPaper.ClassicalFourthNat.BPay_4675
  · exact WuPaper.ClassicalFourthNat.BPay_4676
  · exact WuPaper.ClassicalFourthNat.BPay_4677
  · exact WuPaper.ClassicalFourthNat.BPay_4678
  · exact WuPaper.ClassicalFourthNat.BPay_4679
  · exact WuPaper.ClassicalFourthNat.BPay_4680
  · exact WuPaper.ClassicalFourthNat.BPay_4681
  · exact WuPaper.ClassicalFourthNat.BPay_4682
  · exact WuPaper.ClassicalFourthNat.BPay_4683
  · exact WuPaper.ClassicalFourthNat.BPay_4684
  · exact WuPaper.ClassicalFourthNat.BPay_4685
  · exact WuPaper.ClassicalFourthNat.BPay_4686
  · exact WuPaper.ClassicalFourthNat.BPay_4687
  · exact WuPaper.ClassicalFourthNat.BPay_4688
  · exact WuPaper.ClassicalFourthNat.BPay_4689
  · exact WuPaper.ClassicalFourthNat.BPay_4690
  · exact WuPaper.ClassicalFourthNat.BPay_4691
  · exact WuPaper.ClassicalFourthNat.BPay_4692
  · exact WuPaper.ClassicalFourthNat.BPay_4693
  · exact WuPaper.ClassicalFourthNat.BPay_4694
  · exact WuPaper.ClassicalFourthNat.BPay_4695
  · exact WuPaper.ClassicalFourthNat.BPay_4696
  · exact WuPaper.ClassicalFourthNat.BPay_4697
  · exact WuPaper.ClassicalFourthNat.BPay_4698
  · exact WuPaper.ClassicalFourthNat.BPay_4699
  · exact WuPaper.ClassicalFourthNat.BPay_4700
  · exact WuPaper.ClassicalFourthNat.BPay_4701
  · exact WuPaper.ClassicalFourthNat.BPay_4702
  · exact WuPaper.ClassicalFourthNat.BPay_4703
  · exact WuPaper.ClassicalFourthNat.BPay_4704
  · exact WuPaper.ClassicalFourthNat.BPay_4705
  · exact WuPaper.ClassicalFourthNat.BPay_4706
  · exact WuPaper.ClassicalFourthNat.BPay_4707
  · exact WuPaper.ClassicalFourthNat.BPay_4708
  · exact WuPaper.ClassicalFourthNat.BPay_4709
  · exact WuPaper.ClassicalFourthNat.BPay_4710
  · exact WuPaper.ClassicalFourthNat.BPay_4711
  · exact WuPaper.ClassicalFourthNat.BPay_4712
  · exact WuPaper.ClassicalFourthNat.BPay_4713
  · exact WuPaper.ClassicalFourthNat.BPay_4714
  · exact WuPaper.ClassicalFourthNat.BPay_4715
  · exact WuPaper.ClassicalFourthNat.BPay_4716
  · exact WuPaper.ClassicalFourthNat.BPay_4717
  · exact WuPaper.ClassicalFourthNat.BPay_4718
  · exact WuPaper.ClassicalFourthNat.BPay_4719
  · exact WuPaper.ClassicalFourthNat.BPay_4720
  · exact WuPaper.ClassicalFourthNat.BPay_4721
  · exact WuPaper.ClassicalFourthNat.BPay_4722
  · exact WuPaper.ClassicalFourthNat.BPay_4723
  · exact WuPaper.ClassicalFourthNat.BPay_4724
  · exact WuPaper.ClassicalFourthNat.BPay_4725
  · exact WuPaper.ClassicalFourthNat.BPay_4726
  · exact WuPaper.ClassicalFourthNat.BPay_4727
  · exact WuPaper.ClassicalFourthNat.BPay_4728
  · exact WuPaper.ClassicalFourthNat.BPay_4729
  · exact WuPaper.ClassicalFourthNat.BPay_4730
  · exact WuPaper.ClassicalFourthNat.BPay_4731
  · exact WuPaper.ClassicalFourthNat.BPay_4732
  · exact WuPaper.ClassicalFourthNat.BPay_4733
  · exact WuPaper.ClassicalFourthNat.BPay_4734
  · exact WuPaper.ClassicalFourthNat.BPay_4735
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_073
