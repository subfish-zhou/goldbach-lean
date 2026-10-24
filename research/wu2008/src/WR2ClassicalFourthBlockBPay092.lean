import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay092
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_092 (j : Fin 64) (hj : 64*92+j.val < 10540) :
    BPay (64*92+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5888
  · exact WuPaper.ClassicalFourthNat.BPay_5889
  · exact WuPaper.ClassicalFourthNat.BPay_5890
  · exact WuPaper.ClassicalFourthNat.BPay_5891
  · exact WuPaper.ClassicalFourthNat.BPay_5892
  · exact WuPaper.ClassicalFourthNat.BPay_5893
  · exact WuPaper.ClassicalFourthNat.BPay_5894
  · exact WuPaper.ClassicalFourthNat.BPay_5895
  · exact WuPaper.ClassicalFourthNat.BPay_5896
  · exact WuPaper.ClassicalFourthNat.BPay_5897
  · exact WuPaper.ClassicalFourthNat.BPay_5898
  · exact WuPaper.ClassicalFourthNat.BPay_5899
  · exact WuPaper.ClassicalFourthNat.BPay_5900
  · exact WuPaper.ClassicalFourthNat.BPay_5901
  · exact WuPaper.ClassicalFourthNat.BPay_5902
  · exact WuPaper.ClassicalFourthNat.BPay_5903
  · exact WuPaper.ClassicalFourthNat.BPay_5904
  · exact WuPaper.ClassicalFourthNat.BPay_5905
  · exact WuPaper.ClassicalFourthNat.BPay_5906
  · exact WuPaper.ClassicalFourthNat.BPay_5907
  · exact WuPaper.ClassicalFourthNat.BPay_5908
  · exact WuPaper.ClassicalFourthNat.BPay_5909
  · exact WuPaper.ClassicalFourthNat.BPay_5910
  · exact WuPaper.ClassicalFourthNat.BPay_5911
  · exact WuPaper.ClassicalFourthNat.BPay_5912
  · exact WuPaper.ClassicalFourthNat.BPay_5913
  · exact WuPaper.ClassicalFourthNat.BPay_5914
  · exact WuPaper.ClassicalFourthNat.BPay_5915
  · exact WuPaper.ClassicalFourthNat.BPay_5916
  · exact WuPaper.ClassicalFourthNat.BPay_5917
  · exact WuPaper.ClassicalFourthNat.BPay_5918
  · exact WuPaper.ClassicalFourthNat.BPay_5919
  · exact WuPaper.ClassicalFourthNat.BPay_5920
  · exact WuPaper.ClassicalFourthNat.BPay_5921
  · exact WuPaper.ClassicalFourthNat.BPay_5922
  · exact WuPaper.ClassicalFourthNat.BPay_5923
  · exact WuPaper.ClassicalFourthNat.BPay_5924
  · exact WuPaper.ClassicalFourthNat.BPay_5925
  · exact WuPaper.ClassicalFourthNat.BPay_5926
  · exact WuPaper.ClassicalFourthNat.BPay_5927
  · exact WuPaper.ClassicalFourthNat.BPay_5928
  · exact WuPaper.ClassicalFourthNat.BPay_5929
  · exact WuPaper.ClassicalFourthNat.BPay_5930
  · exact WuPaper.ClassicalFourthNat.BPay_5931
  · exact WuPaper.ClassicalFourthNat.BPay_5932
  · exact WuPaper.ClassicalFourthNat.BPay_5933
  · exact WuPaper.ClassicalFourthNat.BPay_5934
  · exact WuPaper.ClassicalFourthNat.BPay_5935
  · exact WuPaper.ClassicalFourthNat.BPay_5936
  · exact WuPaper.ClassicalFourthNat.BPay_5937
  · exact WuPaper.ClassicalFourthNat.BPay_5938
  · exact WuPaper.ClassicalFourthNat.BPay_5939
  · exact WuPaper.ClassicalFourthNat.BPay_5940
  · exact WuPaper.ClassicalFourthNat.BPay_5941
  · exact WuPaper.ClassicalFourthNat.BPay_5942
  · exact WuPaper.ClassicalFourthNat.BPay_5943
  · exact WuPaper.ClassicalFourthNat.BPay_5944
  · exact WuPaper.ClassicalFourthNat.BPay_5945
  · exact WuPaper.ClassicalFourthNat.BPay_5946
  · exact WuPaper.ClassicalFourthNat.BPay_5947
  · exact WuPaper.ClassicalFourthNat.BPay_5948
  · exact WuPaper.ClassicalFourthNat.BPay_5949
  · exact WuPaper.ClassicalFourthNat.BPay_5950
  · exact WuPaper.ClassicalFourthNat.BPay_5951
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_092
