import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay091
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_091 (j : Fin 64) (hj : 64*91+j.val < 10540) :
    BPay (64*91+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5824
  · exact WuPaper.ClassicalFourthNat.BPay_5825
  · exact WuPaper.ClassicalFourthNat.BPay_5826
  · exact WuPaper.ClassicalFourthNat.BPay_5827
  · exact WuPaper.ClassicalFourthNat.BPay_5828
  · exact WuPaper.ClassicalFourthNat.BPay_5829
  · exact WuPaper.ClassicalFourthNat.BPay_5830
  · exact WuPaper.ClassicalFourthNat.BPay_5831
  · exact WuPaper.ClassicalFourthNat.BPay_5832
  · exact WuPaper.ClassicalFourthNat.BPay_5833
  · exact WuPaper.ClassicalFourthNat.BPay_5834
  · exact WuPaper.ClassicalFourthNat.BPay_5835
  · exact WuPaper.ClassicalFourthNat.BPay_5836
  · exact WuPaper.ClassicalFourthNat.BPay_5837
  · exact WuPaper.ClassicalFourthNat.BPay_5838
  · exact WuPaper.ClassicalFourthNat.BPay_5839
  · exact WuPaper.ClassicalFourthNat.BPay_5840
  · exact WuPaper.ClassicalFourthNat.BPay_5841
  · exact WuPaper.ClassicalFourthNat.BPay_5842
  · exact WuPaper.ClassicalFourthNat.BPay_5843
  · exact WuPaper.ClassicalFourthNat.BPay_5844
  · exact WuPaper.ClassicalFourthNat.BPay_5845
  · exact WuPaper.ClassicalFourthNat.BPay_5846
  · exact WuPaper.ClassicalFourthNat.BPay_5847
  · exact WuPaper.ClassicalFourthNat.BPay_5848
  · exact WuPaper.ClassicalFourthNat.BPay_5849
  · exact WuPaper.ClassicalFourthNat.BPay_5850
  · exact WuPaper.ClassicalFourthNat.BPay_5851
  · exact WuPaper.ClassicalFourthNat.BPay_5852
  · exact WuPaper.ClassicalFourthNat.BPay_5853
  · exact WuPaper.ClassicalFourthNat.BPay_5854
  · exact WuPaper.ClassicalFourthNat.BPay_5855
  · exact WuPaper.ClassicalFourthNat.BPay_5856
  · exact WuPaper.ClassicalFourthNat.BPay_5857
  · exact WuPaper.ClassicalFourthNat.BPay_5858
  · exact WuPaper.ClassicalFourthNat.BPay_5859
  · exact WuPaper.ClassicalFourthNat.BPay_5860
  · exact WuPaper.ClassicalFourthNat.BPay_5861
  · exact WuPaper.ClassicalFourthNat.BPay_5862
  · exact WuPaper.ClassicalFourthNat.BPay_5863
  · exact WuPaper.ClassicalFourthNat.BPay_5864
  · exact WuPaper.ClassicalFourthNat.BPay_5865
  · exact WuPaper.ClassicalFourthNat.BPay_5866
  · exact WuPaper.ClassicalFourthNat.BPay_5867
  · exact WuPaper.ClassicalFourthNat.BPay_5868
  · exact WuPaper.ClassicalFourthNat.BPay_5869
  · exact WuPaper.ClassicalFourthNat.BPay_5870
  · exact WuPaper.ClassicalFourthNat.BPay_5871
  · exact WuPaper.ClassicalFourthNat.BPay_5872
  · exact WuPaper.ClassicalFourthNat.BPay_5873
  · exact WuPaper.ClassicalFourthNat.BPay_5874
  · exact WuPaper.ClassicalFourthNat.BPay_5875
  · exact WuPaper.ClassicalFourthNat.BPay_5876
  · exact WuPaper.ClassicalFourthNat.BPay_5877
  · exact WuPaper.ClassicalFourthNat.BPay_5878
  · exact WuPaper.ClassicalFourthNat.BPay_5879
  · exact WuPaper.ClassicalFourthNat.BPay_5880
  · exact WuPaper.ClassicalFourthNat.BPay_5881
  · exact WuPaper.ClassicalFourthNat.BPay_5882
  · exact WuPaper.ClassicalFourthNat.BPay_5883
  · exact WuPaper.ClassicalFourthNat.BPay_5884
  · exact WuPaper.ClassicalFourthNat.BPay_5885
  · exact WuPaper.ClassicalFourthNat.BPay_5886
  · exact WuPaper.ClassicalFourthNat.BPay_5887
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_091
