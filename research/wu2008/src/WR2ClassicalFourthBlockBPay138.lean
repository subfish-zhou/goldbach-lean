import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay138
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_138 (j : Fin 64) (hj : 64*138+j.val < 10540) :
    BPay (64*138+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8832
  · exact WuPaper.ClassicalFourthNat.BPay_8833
  · exact WuPaper.ClassicalFourthNat.BPay_8834
  · exact WuPaper.ClassicalFourthNat.BPay_8835
  · exact WuPaper.ClassicalFourthNat.BPay_8836
  · exact WuPaper.ClassicalFourthNat.BPay_8837
  · exact WuPaper.ClassicalFourthNat.BPay_8838
  · exact WuPaper.ClassicalFourthNat.BPay_8839
  · exact WuPaper.ClassicalFourthNat.BPay_8840
  · exact WuPaper.ClassicalFourthNat.BPay_8841
  · exact WuPaper.ClassicalFourthNat.BPay_8842
  · exact WuPaper.ClassicalFourthNat.BPay_8843
  · exact WuPaper.ClassicalFourthNat.BPay_8844
  · exact WuPaper.ClassicalFourthNat.BPay_8845
  · exact WuPaper.ClassicalFourthNat.BPay_8846
  · exact WuPaper.ClassicalFourthNat.BPay_8847
  · exact WuPaper.ClassicalFourthNat.BPay_8848
  · exact WuPaper.ClassicalFourthNat.BPay_8849
  · exact WuPaper.ClassicalFourthNat.BPay_8850
  · exact WuPaper.ClassicalFourthNat.BPay_8851
  · exact WuPaper.ClassicalFourthNat.BPay_8852
  · exact WuPaper.ClassicalFourthNat.BPay_8853
  · exact WuPaper.ClassicalFourthNat.BPay_8854
  · exact WuPaper.ClassicalFourthNat.BPay_8855
  · exact WuPaper.ClassicalFourthNat.BPay_8856
  · exact WuPaper.ClassicalFourthNat.BPay_8857
  · exact WuPaper.ClassicalFourthNat.BPay_8858
  · exact WuPaper.ClassicalFourthNat.BPay_8859
  · exact WuPaper.ClassicalFourthNat.BPay_8860
  · exact WuPaper.ClassicalFourthNat.BPay_8861
  · exact WuPaper.ClassicalFourthNat.BPay_8862
  · exact WuPaper.ClassicalFourthNat.BPay_8863
  · exact WuPaper.ClassicalFourthNat.BPay_8864
  · exact WuPaper.ClassicalFourthNat.BPay_8865
  · exact WuPaper.ClassicalFourthNat.BPay_8866
  · exact WuPaper.ClassicalFourthNat.BPay_8867
  · exact WuPaper.ClassicalFourthNat.BPay_8868
  · exact WuPaper.ClassicalFourthNat.BPay_8869
  · exact WuPaper.ClassicalFourthNat.BPay_8870
  · exact WuPaper.ClassicalFourthNat.BPay_8871
  · exact WuPaper.ClassicalFourthNat.BPay_8872
  · exact WuPaper.ClassicalFourthNat.BPay_8873
  · exact WuPaper.ClassicalFourthNat.BPay_8874
  · exact WuPaper.ClassicalFourthNat.BPay_8875
  · exact WuPaper.ClassicalFourthNat.BPay_8876
  · exact WuPaper.ClassicalFourthNat.BPay_8877
  · exact WuPaper.ClassicalFourthNat.BPay_8878
  · exact WuPaper.ClassicalFourthNat.BPay_8879
  · exact WuPaper.ClassicalFourthNat.BPay_8880
  · exact WuPaper.ClassicalFourthNat.BPay_8881
  · exact WuPaper.ClassicalFourthNat.BPay_8882
  · exact WuPaper.ClassicalFourthNat.BPay_8883
  · exact WuPaper.ClassicalFourthNat.BPay_8884
  · exact WuPaper.ClassicalFourthNat.BPay_8885
  · exact WuPaper.ClassicalFourthNat.BPay_8886
  · exact WuPaper.ClassicalFourthNat.BPay_8887
  · exact WuPaper.ClassicalFourthNat.BPay_8888
  · exact WuPaper.ClassicalFourthNat.BPay_8889
  · exact WuPaper.ClassicalFourthNat.BPay_8890
  · exact WuPaper.ClassicalFourthNat.BPay_8891
  · exact WuPaper.ClassicalFourthNat.BPay_8892
  · exact WuPaper.ClassicalFourthNat.BPay_8893
  · exact WuPaper.ClassicalFourthNat.BPay_8894
  · exact WuPaper.ClassicalFourthNat.BPay_8895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_138
