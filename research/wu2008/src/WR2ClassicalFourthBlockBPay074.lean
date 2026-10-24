import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay074
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_074 (j : Fin 64) (hj : 64*74+j.val < 10540) :
    BPay (64*74+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4736
  · exact WuPaper.ClassicalFourthNat.BPay_4737
  · exact WuPaper.ClassicalFourthNat.BPay_4738
  · exact WuPaper.ClassicalFourthNat.BPay_4739
  · exact WuPaper.ClassicalFourthNat.BPay_4740
  · exact WuPaper.ClassicalFourthNat.BPay_4741
  · exact WuPaper.ClassicalFourthNat.BPay_4742
  · exact WuPaper.ClassicalFourthNat.BPay_4743
  · exact WuPaper.ClassicalFourthNat.BPay_4744
  · exact WuPaper.ClassicalFourthNat.BPay_4745
  · exact WuPaper.ClassicalFourthNat.BPay_4746
  · exact WuPaper.ClassicalFourthNat.BPay_4747
  · exact WuPaper.ClassicalFourthNat.BPay_4748
  · exact WuPaper.ClassicalFourthNat.BPay_4749
  · exact WuPaper.ClassicalFourthNat.BPay_4750
  · exact WuPaper.ClassicalFourthNat.BPay_4751
  · exact WuPaper.ClassicalFourthNat.BPay_4752
  · exact WuPaper.ClassicalFourthNat.BPay_4753
  · exact WuPaper.ClassicalFourthNat.BPay_4754
  · exact WuPaper.ClassicalFourthNat.BPay_4755
  · exact WuPaper.ClassicalFourthNat.BPay_4756
  · exact WuPaper.ClassicalFourthNat.BPay_4757
  · exact WuPaper.ClassicalFourthNat.BPay_4758
  · exact WuPaper.ClassicalFourthNat.BPay_4759
  · exact WuPaper.ClassicalFourthNat.BPay_4760
  · exact WuPaper.ClassicalFourthNat.BPay_4761
  · exact WuPaper.ClassicalFourthNat.BPay_4762
  · exact WuPaper.ClassicalFourthNat.BPay_4763
  · exact WuPaper.ClassicalFourthNat.BPay_4764
  · exact WuPaper.ClassicalFourthNat.BPay_4765
  · exact WuPaper.ClassicalFourthNat.BPay_4766
  · exact WuPaper.ClassicalFourthNat.BPay_4767
  · exact WuPaper.ClassicalFourthNat.BPay_4768
  · exact WuPaper.ClassicalFourthNat.BPay_4769
  · exact WuPaper.ClassicalFourthNat.BPay_4770
  · exact WuPaper.ClassicalFourthNat.BPay_4771
  · exact WuPaper.ClassicalFourthNat.BPay_4772
  · exact WuPaper.ClassicalFourthNat.BPay_4773
  · exact WuPaper.ClassicalFourthNat.BPay_4774
  · exact WuPaper.ClassicalFourthNat.BPay_4775
  · exact WuPaper.ClassicalFourthNat.BPay_4776
  · exact WuPaper.ClassicalFourthNat.BPay_4777
  · exact WuPaper.ClassicalFourthNat.BPay_4778
  · exact WuPaper.ClassicalFourthNat.BPay_4779
  · exact WuPaper.ClassicalFourthNat.BPay_4780
  · exact WuPaper.ClassicalFourthNat.BPay_4781
  · exact WuPaper.ClassicalFourthNat.BPay_4782
  · exact WuPaper.ClassicalFourthNat.BPay_4783
  · exact WuPaper.ClassicalFourthNat.BPay_4784
  · exact WuPaper.ClassicalFourthNat.BPay_4785
  · exact WuPaper.ClassicalFourthNat.BPay_4786
  · exact WuPaper.ClassicalFourthNat.BPay_4787
  · exact WuPaper.ClassicalFourthNat.BPay_4788
  · exact WuPaper.ClassicalFourthNat.BPay_4789
  · exact WuPaper.ClassicalFourthNat.BPay_4790
  · exact WuPaper.ClassicalFourthNat.BPay_4791
  · exact WuPaper.ClassicalFourthNat.BPay_4792
  · exact WuPaper.ClassicalFourthNat.BPay_4793
  · exact WuPaper.ClassicalFourthNat.BPay_4794
  · exact WuPaper.ClassicalFourthNat.BPay_4795
  · exact WuPaper.ClassicalFourthNat.BPay_4796
  · exact WuPaper.ClassicalFourthNat.BPay_4797
  · exact WuPaper.ClassicalFourthNat.BPay_4798
  · exact WuPaper.ClassicalFourthNat.BPay_4799
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_074
