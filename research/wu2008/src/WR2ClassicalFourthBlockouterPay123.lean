import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay123
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_123 (j : Fin 64) (hj : 64*123+j.val < 10540) :
    OuterPay (64*123+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_7872
  · exact WuPaper.ClassicalFourthNat.outerPay_7873
  · exact WuPaper.ClassicalFourthNat.outerPay_7874
  · exact WuPaper.ClassicalFourthNat.outerPay_7875
  · exact WuPaper.ClassicalFourthNat.outerPay_7876
  · exact WuPaper.ClassicalFourthNat.outerPay_7877
  · exact WuPaper.ClassicalFourthNat.outerPay_7878
  · exact WuPaper.ClassicalFourthNat.outerPay_7879
  · exact WuPaper.ClassicalFourthNat.outerPay_7880
  · exact WuPaper.ClassicalFourthNat.outerPay_7881
  · exact WuPaper.ClassicalFourthNat.outerPay_7882
  · exact WuPaper.ClassicalFourthNat.outerPay_7883
  · exact WuPaper.ClassicalFourthNat.outerPay_7884
  · exact WuPaper.ClassicalFourthNat.outerPay_7885
  · exact WuPaper.ClassicalFourthNat.outerPay_7886
  · exact WuPaper.ClassicalFourthNat.outerPay_7887
  · exact WuPaper.ClassicalFourthNat.outerPay_7888
  · exact WuPaper.ClassicalFourthNat.outerPay_7889
  · exact WuPaper.ClassicalFourthNat.outerPay_7890
  · exact WuPaper.ClassicalFourthNat.outerPay_7891
  · exact WuPaper.ClassicalFourthNat.outerPay_7892
  · exact WuPaper.ClassicalFourthNat.outerPay_7893
  · exact WuPaper.ClassicalFourthNat.outerPay_7894
  · exact WuPaper.ClassicalFourthNat.outerPay_7895
  · exact WuPaper.ClassicalFourthNat.outerPay_7896
  · exact WuPaper.ClassicalFourthNat.outerPay_7897
  · exact WuPaper.ClassicalFourthNat.outerPay_7898
  · exact WuPaper.ClassicalFourthNat.outerPay_7899
  · exact WuPaper.ClassicalFourthNat.outerPay_7900
  · exact WuPaper.ClassicalFourthNat.outerPay_7901
  · exact WuPaper.ClassicalFourthNat.outerPay_7902
  · exact WuPaper.ClassicalFourthNat.outerPay_7903
  · exact WuPaper.ClassicalFourthNat.outerPay_7904
  · exact WuPaper.ClassicalFourthNat.outerPay_7905
  · exact WuPaper.ClassicalFourthNat.outerPay_7906
  · exact WuPaper.ClassicalFourthNat.outerPay_7907
  · exact WuPaper.ClassicalFourthNat.outerPay_7908
  · exact WuPaper.ClassicalFourthNat.outerPay_7909
  · exact WuPaper.ClassicalFourthNat.outerPay_7910
  · exact WuPaper.ClassicalFourthNat.outerPay_7911
  · exact WuPaper.ClassicalFourthNat.outerPay_7912
  · exact WuPaper.ClassicalFourthNat.outerPay_7913
  · exact WuPaper.ClassicalFourthNat.outerPay_7914
  · exact WuPaper.ClassicalFourthNat.outerPay_7915
  · exact WuPaper.ClassicalFourthNat.outerPay_7916
  · exact WuPaper.ClassicalFourthNat.outerPay_7917
  · exact WuPaper.ClassicalFourthNat.outerPay_7918
  · exact WuPaper.ClassicalFourthNat.outerPay_7919
  · exact WuPaper.ClassicalFourthNat.outerPay_7920
  · exact WuPaper.ClassicalFourthNat.outerPay_7921
  · exact WuPaper.ClassicalFourthNat.outerPay_7922
  · exact WuPaper.ClassicalFourthNat.outerPay_7923
  · exact WuPaper.ClassicalFourthNat.outerPay_7924
  · exact WuPaper.ClassicalFourthNat.outerPay_7925
  · exact WuPaper.ClassicalFourthNat.outerPay_7926
  · exact WuPaper.ClassicalFourthNat.outerPay_7927
  · exact WuPaper.ClassicalFourthNat.outerPay_7928
  · exact WuPaper.ClassicalFourthNat.outerPay_7929
  · exact WuPaper.ClassicalFourthNat.outerPay_7930
  · exact WuPaper.ClassicalFourthNat.outerPay_7931
  · exact WuPaper.ClassicalFourthNat.outerPay_7932
  · exact WuPaper.ClassicalFourthNat.outerPay_7933
  · exact WuPaper.ClassicalFourthNat.outerPay_7934
  · exact WuPaper.ClassicalFourthNat.outerPay_7935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_123
