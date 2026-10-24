import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint014
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_014 (j : Fin 64) (hj : 64*14+j.val < 10541) :
    OuterPoint (64*14+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_896
  · exact WuPaper.ClassicalFourthNat.OuterPoint_897
  · exact WuPaper.ClassicalFourthNat.OuterPoint_898
  · exact WuPaper.ClassicalFourthNat.OuterPoint_899
  · exact WuPaper.ClassicalFourthNat.OuterPoint_900
  · exact WuPaper.ClassicalFourthNat.OuterPoint_901
  · exact WuPaper.ClassicalFourthNat.OuterPoint_902
  · exact WuPaper.ClassicalFourthNat.OuterPoint_903
  · exact WuPaper.ClassicalFourthNat.OuterPoint_904
  · exact WuPaper.ClassicalFourthNat.OuterPoint_905
  · exact WuPaper.ClassicalFourthNat.OuterPoint_906
  · exact WuPaper.ClassicalFourthNat.OuterPoint_907
  · exact WuPaper.ClassicalFourthNat.OuterPoint_908
  · exact WuPaper.ClassicalFourthNat.OuterPoint_909
  · exact WuPaper.ClassicalFourthNat.OuterPoint_910
  · exact WuPaper.ClassicalFourthNat.OuterPoint_911
  · exact WuPaper.ClassicalFourthNat.OuterPoint_912
  · exact WuPaper.ClassicalFourthNat.OuterPoint_913
  · exact WuPaper.ClassicalFourthNat.OuterPoint_914
  · exact WuPaper.ClassicalFourthNat.OuterPoint_915
  · exact WuPaper.ClassicalFourthNat.OuterPoint_916
  · exact WuPaper.ClassicalFourthNat.OuterPoint_917
  · exact WuPaper.ClassicalFourthNat.OuterPoint_918
  · exact WuPaper.ClassicalFourthNat.OuterPoint_919
  · exact WuPaper.ClassicalFourthNat.OuterPoint_920
  · exact WuPaper.ClassicalFourthNat.OuterPoint_921
  · exact WuPaper.ClassicalFourthNat.OuterPoint_922
  · exact WuPaper.ClassicalFourthNat.OuterPoint_923
  · exact WuPaper.ClassicalFourthNat.OuterPoint_924
  · exact WuPaper.ClassicalFourthNat.OuterPoint_925
  · exact WuPaper.ClassicalFourthNat.OuterPoint_926
  · exact WuPaper.ClassicalFourthNat.OuterPoint_927
  · exact WuPaper.ClassicalFourthNat.OuterPoint_928
  · exact WuPaper.ClassicalFourthNat.OuterPoint_929
  · exact WuPaper.ClassicalFourthNat.OuterPoint_930
  · exact WuPaper.ClassicalFourthNat.OuterPoint_931
  · exact WuPaper.ClassicalFourthNat.OuterPoint_932
  · exact WuPaper.ClassicalFourthNat.OuterPoint_933
  · exact WuPaper.ClassicalFourthNat.OuterPoint_934
  · exact WuPaper.ClassicalFourthNat.OuterPoint_935
  · exact WuPaper.ClassicalFourthNat.OuterPoint_936
  · exact WuPaper.ClassicalFourthNat.OuterPoint_937
  · exact WuPaper.ClassicalFourthNat.OuterPoint_938
  · exact WuPaper.ClassicalFourthNat.OuterPoint_939
  · exact WuPaper.ClassicalFourthNat.OuterPoint_940
  · exact WuPaper.ClassicalFourthNat.OuterPoint_941
  · exact WuPaper.ClassicalFourthNat.OuterPoint_942
  · exact WuPaper.ClassicalFourthNat.OuterPoint_943
  · exact WuPaper.ClassicalFourthNat.OuterPoint_944
  · exact WuPaper.ClassicalFourthNat.OuterPoint_945
  · exact WuPaper.ClassicalFourthNat.OuterPoint_946
  · exact WuPaper.ClassicalFourthNat.OuterPoint_947
  · exact WuPaper.ClassicalFourthNat.OuterPoint_948
  · exact WuPaper.ClassicalFourthNat.OuterPoint_949
  · exact WuPaper.ClassicalFourthNat.OuterPoint_950
  · exact WuPaper.ClassicalFourthNat.OuterPoint_951
  · exact WuPaper.ClassicalFourthNat.OuterPoint_952
  · exact WuPaper.ClassicalFourthNat.OuterPoint_953
  · exact WuPaper.ClassicalFourthNat.OuterPoint_954
  · exact WuPaper.ClassicalFourthNat.OuterPoint_955
  · exact WuPaper.ClassicalFourthNat.OuterPoint_956
  · exact WuPaper.ClassicalFourthNat.OuterPoint_957
  · exact WuPaper.ClassicalFourthNat.OuterPoint_958
  · exact WuPaper.ClassicalFourthNat.OuterPoint_959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_014
