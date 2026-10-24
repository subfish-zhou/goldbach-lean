import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay153
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_153 (j : Fin 64) (hj : 64*153+j.val < 10540) :
    BPay (64*153+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9792
  · exact WuPaper.ClassicalFourthNat.BPay_9793
  · exact WuPaper.ClassicalFourthNat.BPay_9794
  · exact WuPaper.ClassicalFourthNat.BPay_9795
  · exact WuPaper.ClassicalFourthNat.BPay_9796
  · exact WuPaper.ClassicalFourthNat.BPay_9797
  · exact WuPaper.ClassicalFourthNat.BPay_9798
  · exact WuPaper.ClassicalFourthNat.BPay_9799
  · exact WuPaper.ClassicalFourthNat.BPay_9800
  · exact WuPaper.ClassicalFourthNat.BPay_9801
  · exact WuPaper.ClassicalFourthNat.BPay_9802
  · exact WuPaper.ClassicalFourthNat.BPay_9803
  · exact WuPaper.ClassicalFourthNat.BPay_9804
  · exact WuPaper.ClassicalFourthNat.BPay_9805
  · exact WuPaper.ClassicalFourthNat.BPay_9806
  · exact WuPaper.ClassicalFourthNat.BPay_9807
  · exact WuPaper.ClassicalFourthNat.BPay_9808
  · exact WuPaper.ClassicalFourthNat.BPay_9809
  · exact WuPaper.ClassicalFourthNat.BPay_9810
  · exact WuPaper.ClassicalFourthNat.BPay_9811
  · exact WuPaper.ClassicalFourthNat.BPay_9812
  · exact WuPaper.ClassicalFourthNat.BPay_9813
  · exact WuPaper.ClassicalFourthNat.BPay_9814
  · exact WuPaper.ClassicalFourthNat.BPay_9815
  · exact WuPaper.ClassicalFourthNat.BPay_9816
  · exact WuPaper.ClassicalFourthNat.BPay_9817
  · exact WuPaper.ClassicalFourthNat.BPay_9818
  · exact WuPaper.ClassicalFourthNat.BPay_9819
  · exact WuPaper.ClassicalFourthNat.BPay_9820
  · exact WuPaper.ClassicalFourthNat.BPay_9821
  · exact WuPaper.ClassicalFourthNat.BPay_9822
  · exact WuPaper.ClassicalFourthNat.BPay_9823
  · exact WuPaper.ClassicalFourthNat.BPay_9824
  · exact WuPaper.ClassicalFourthNat.BPay_9825
  · exact WuPaper.ClassicalFourthNat.BPay_9826
  · exact WuPaper.ClassicalFourthNat.BPay_9827
  · exact WuPaper.ClassicalFourthNat.BPay_9828
  · exact WuPaper.ClassicalFourthNat.BPay_9829
  · exact WuPaper.ClassicalFourthNat.BPay_9830
  · exact WuPaper.ClassicalFourthNat.BPay_9831
  · exact WuPaper.ClassicalFourthNat.BPay_9832
  · exact WuPaper.ClassicalFourthNat.BPay_9833
  · exact WuPaper.ClassicalFourthNat.BPay_9834
  · exact WuPaper.ClassicalFourthNat.BPay_9835
  · exact WuPaper.ClassicalFourthNat.BPay_9836
  · exact WuPaper.ClassicalFourthNat.BPay_9837
  · exact WuPaper.ClassicalFourthNat.BPay_9838
  · exact WuPaper.ClassicalFourthNat.BPay_9839
  · exact WuPaper.ClassicalFourthNat.BPay_9840
  · exact WuPaper.ClassicalFourthNat.BPay_9841
  · exact WuPaper.ClassicalFourthNat.BPay_9842
  · exact WuPaper.ClassicalFourthNat.BPay_9843
  · exact WuPaper.ClassicalFourthNat.BPay_9844
  · exact WuPaper.ClassicalFourthNat.BPay_9845
  · exact WuPaper.ClassicalFourthNat.BPay_9846
  · exact WuPaper.ClassicalFourthNat.BPay_9847
  · exact WuPaper.ClassicalFourthNat.BPay_9848
  · exact WuPaper.ClassicalFourthNat.BPay_9849
  · exact WuPaper.ClassicalFourthNat.BPay_9850
  · exact WuPaper.ClassicalFourthNat.BPay_9851
  · exact WuPaper.ClassicalFourthNat.BPay_9852
  · exact WuPaper.ClassicalFourthNat.BPay_9853
  · exact WuPaper.ClassicalFourthNat.BPay_9854
  · exact WuPaper.ClassicalFourthNat.BPay_9855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_153
