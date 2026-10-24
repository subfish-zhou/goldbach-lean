import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint123
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_123 (j : Fin 64) (hj : 64*123+j.val < 10541) :
    OuterPoint (64*123+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7872
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7873
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7874
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7875
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7876
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7877
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7878
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7879
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7880
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7881
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7882
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7883
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7884
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7885
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7886
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7887
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7888
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7889
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7890
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7891
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7892
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7893
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7894
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7895
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7896
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7897
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7898
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7899
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7900
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7901
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7902
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7903
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7904
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7905
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7906
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7907
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7908
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7909
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7910
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7911
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7912
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7913
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7914
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7915
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7916
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7917
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7918
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7919
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7920
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7921
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7922
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7923
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7924
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7925
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7926
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7927
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7928
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7929
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7930
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7931
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7932
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7933
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7934
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_123
