import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay123
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_123 (j : Fin 64) (hj : 64*123+j.val < 10540) :
    BPay (64*123+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7872
  · exact WuPaper.ClassicalFourthNat.BPay_7873
  · exact WuPaper.ClassicalFourthNat.BPay_7874
  · exact WuPaper.ClassicalFourthNat.BPay_7875
  · exact WuPaper.ClassicalFourthNat.BPay_7876
  · exact WuPaper.ClassicalFourthNat.BPay_7877
  · exact WuPaper.ClassicalFourthNat.BPay_7878
  · exact WuPaper.ClassicalFourthNat.BPay_7879
  · exact WuPaper.ClassicalFourthNat.BPay_7880
  · exact WuPaper.ClassicalFourthNat.BPay_7881
  · exact WuPaper.ClassicalFourthNat.BPay_7882
  · exact WuPaper.ClassicalFourthNat.BPay_7883
  · exact WuPaper.ClassicalFourthNat.BPay_7884
  · exact WuPaper.ClassicalFourthNat.BPay_7885
  · exact WuPaper.ClassicalFourthNat.BPay_7886
  · exact WuPaper.ClassicalFourthNat.BPay_7887
  · exact WuPaper.ClassicalFourthNat.BPay_7888
  · exact WuPaper.ClassicalFourthNat.BPay_7889
  · exact WuPaper.ClassicalFourthNat.BPay_7890
  · exact WuPaper.ClassicalFourthNat.BPay_7891
  · exact WuPaper.ClassicalFourthNat.BPay_7892
  · exact WuPaper.ClassicalFourthNat.BPay_7893
  · exact WuPaper.ClassicalFourthNat.BPay_7894
  · exact WuPaper.ClassicalFourthNat.BPay_7895
  · exact WuPaper.ClassicalFourthNat.BPay_7896
  · exact WuPaper.ClassicalFourthNat.BPay_7897
  · exact WuPaper.ClassicalFourthNat.BPay_7898
  · exact WuPaper.ClassicalFourthNat.BPay_7899
  · exact WuPaper.ClassicalFourthNat.BPay_7900
  · exact WuPaper.ClassicalFourthNat.BPay_7901
  · exact WuPaper.ClassicalFourthNat.BPay_7902
  · exact WuPaper.ClassicalFourthNat.BPay_7903
  · exact WuPaper.ClassicalFourthNat.BPay_7904
  · exact WuPaper.ClassicalFourthNat.BPay_7905
  · exact WuPaper.ClassicalFourthNat.BPay_7906
  · exact WuPaper.ClassicalFourthNat.BPay_7907
  · exact WuPaper.ClassicalFourthNat.BPay_7908
  · exact WuPaper.ClassicalFourthNat.BPay_7909
  · exact WuPaper.ClassicalFourthNat.BPay_7910
  · exact WuPaper.ClassicalFourthNat.BPay_7911
  · exact WuPaper.ClassicalFourthNat.BPay_7912
  · exact WuPaper.ClassicalFourthNat.BPay_7913
  · exact WuPaper.ClassicalFourthNat.BPay_7914
  · exact WuPaper.ClassicalFourthNat.BPay_7915
  · exact WuPaper.ClassicalFourthNat.BPay_7916
  · exact WuPaper.ClassicalFourthNat.BPay_7917
  · exact WuPaper.ClassicalFourthNat.BPay_7918
  · exact WuPaper.ClassicalFourthNat.BPay_7919
  · exact WuPaper.ClassicalFourthNat.BPay_7920
  · exact WuPaper.ClassicalFourthNat.BPay_7921
  · exact WuPaper.ClassicalFourthNat.BPay_7922
  · exact WuPaper.ClassicalFourthNat.BPay_7923
  · exact WuPaper.ClassicalFourthNat.BPay_7924
  · exact WuPaper.ClassicalFourthNat.BPay_7925
  · exact WuPaper.ClassicalFourthNat.BPay_7926
  · exact WuPaper.ClassicalFourthNat.BPay_7927
  · exact WuPaper.ClassicalFourthNat.BPay_7928
  · exact WuPaper.ClassicalFourthNat.BPay_7929
  · exact WuPaper.ClassicalFourthNat.BPay_7930
  · exact WuPaper.ClassicalFourthNat.BPay_7931
  · exact WuPaper.ClassicalFourthNat.BPay_7932
  · exact WuPaper.ClassicalFourthNat.BPay_7933
  · exact WuPaper.ClassicalFourthNat.BPay_7934
  · exact WuPaper.ClassicalFourthNat.BPay_7935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_123
