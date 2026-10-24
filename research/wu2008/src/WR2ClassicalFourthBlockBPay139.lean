import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay139
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_139 (j : Fin 64) (hj : 64*139+j.val < 10540) :
    BPay (64*139+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8896
  · exact WuPaper.ClassicalFourthNat.BPay_8897
  · exact WuPaper.ClassicalFourthNat.BPay_8898
  · exact WuPaper.ClassicalFourthNat.BPay_8899
  · exact WuPaper.ClassicalFourthNat.BPay_8900
  · exact WuPaper.ClassicalFourthNat.BPay_8901
  · exact WuPaper.ClassicalFourthNat.BPay_8902
  · exact WuPaper.ClassicalFourthNat.BPay_8903
  · exact WuPaper.ClassicalFourthNat.BPay_8904
  · exact WuPaper.ClassicalFourthNat.BPay_8905
  · exact WuPaper.ClassicalFourthNat.BPay_8906
  · exact WuPaper.ClassicalFourthNat.BPay_8907
  · exact WuPaper.ClassicalFourthNat.BPay_8908
  · exact WuPaper.ClassicalFourthNat.BPay_8909
  · exact WuPaper.ClassicalFourthNat.BPay_8910
  · exact WuPaper.ClassicalFourthNat.BPay_8911
  · exact WuPaper.ClassicalFourthNat.BPay_8912
  · exact WuPaper.ClassicalFourthNat.BPay_8913
  · exact WuPaper.ClassicalFourthNat.BPay_8914
  · exact WuPaper.ClassicalFourthNat.BPay_8915
  · exact WuPaper.ClassicalFourthNat.BPay_8916
  · exact WuPaper.ClassicalFourthNat.BPay_8917
  · exact WuPaper.ClassicalFourthNat.BPay_8918
  · exact WuPaper.ClassicalFourthNat.BPay_8919
  · exact WuPaper.ClassicalFourthNat.BPay_8920
  · exact WuPaper.ClassicalFourthNat.BPay_8921
  · exact WuPaper.ClassicalFourthNat.BPay_8922
  · exact WuPaper.ClassicalFourthNat.BPay_8923
  · exact WuPaper.ClassicalFourthNat.BPay_8924
  · exact WuPaper.ClassicalFourthNat.BPay_8925
  · exact WuPaper.ClassicalFourthNat.BPay_8926
  · exact WuPaper.ClassicalFourthNat.BPay_8927
  · exact WuPaper.ClassicalFourthNat.BPay_8928
  · exact WuPaper.ClassicalFourthNat.BPay_8929
  · exact WuPaper.ClassicalFourthNat.BPay_8930
  · exact WuPaper.ClassicalFourthNat.BPay_8931
  · exact WuPaper.ClassicalFourthNat.BPay_8932
  · exact WuPaper.ClassicalFourthNat.BPay_8933
  · exact WuPaper.ClassicalFourthNat.BPay_8934
  · exact WuPaper.ClassicalFourthNat.BPay_8935
  · exact WuPaper.ClassicalFourthNat.BPay_8936
  · exact WuPaper.ClassicalFourthNat.BPay_8937
  · exact WuPaper.ClassicalFourthNat.BPay_8938
  · exact WuPaper.ClassicalFourthNat.BPay_8939
  · exact WuPaper.ClassicalFourthNat.BPay_8940
  · exact WuPaper.ClassicalFourthNat.BPay_8941
  · exact WuPaper.ClassicalFourthNat.BPay_8942
  · exact WuPaper.ClassicalFourthNat.BPay_8943
  · exact WuPaper.ClassicalFourthNat.BPay_8944
  · exact WuPaper.ClassicalFourthNat.BPay_8945
  · exact WuPaper.ClassicalFourthNat.BPay_8946
  · exact WuPaper.ClassicalFourthNat.BPay_8947
  · exact WuPaper.ClassicalFourthNat.BPay_8948
  · exact WuPaper.ClassicalFourthNat.BPay_8949
  · exact WuPaper.ClassicalFourthNat.BPay_8950
  · exact WuPaper.ClassicalFourthNat.BPay_8951
  · exact WuPaper.ClassicalFourthNat.BPay_8952
  · exact WuPaper.ClassicalFourthNat.BPay_8953
  · exact WuPaper.ClassicalFourthNat.BPay_8954
  · exact WuPaper.ClassicalFourthNat.BPay_8955
  · exact WuPaper.ClassicalFourthNat.BPay_8956
  · exact WuPaper.ClassicalFourthNat.BPay_8957
  · exact WuPaper.ClassicalFourthNat.BPay_8958
  · exact WuPaper.ClassicalFourthNat.BPay_8959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_139
