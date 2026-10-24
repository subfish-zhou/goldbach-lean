import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay014
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_014 (j : Fin 64) (hj : 64*14+j.val < 2540) :
    CPay (64*14+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_896
  · exact WuPaper.ClassicalFourthNat.CPay_897
  · exact WuPaper.ClassicalFourthNat.CPay_898
  · exact WuPaper.ClassicalFourthNat.CPay_899
  · exact WuPaper.ClassicalFourthNat.CPay_900
  · exact WuPaper.ClassicalFourthNat.CPay_901
  · exact WuPaper.ClassicalFourthNat.CPay_902
  · exact WuPaper.ClassicalFourthNat.CPay_903
  · exact WuPaper.ClassicalFourthNat.CPay_904
  · exact WuPaper.ClassicalFourthNat.CPay_905
  · exact WuPaper.ClassicalFourthNat.CPay_906
  · exact WuPaper.ClassicalFourthNat.CPay_907
  · exact WuPaper.ClassicalFourthNat.CPay_908
  · exact WuPaper.ClassicalFourthNat.CPay_909
  · exact WuPaper.ClassicalFourthNat.CPay_910
  · exact WuPaper.ClassicalFourthNat.CPay_911
  · exact WuPaper.ClassicalFourthNat.CPay_912
  · exact WuPaper.ClassicalFourthNat.CPay_913
  · exact WuPaper.ClassicalFourthNat.CPay_914
  · exact WuPaper.ClassicalFourthNat.CPay_915
  · exact WuPaper.ClassicalFourthNat.CPay_916
  · exact WuPaper.ClassicalFourthNat.CPay_917
  · exact WuPaper.ClassicalFourthNat.CPay_918
  · exact WuPaper.ClassicalFourthNat.CPay_919
  · exact WuPaper.ClassicalFourthNat.CPay_920
  · exact WuPaper.ClassicalFourthNat.CPay_921
  · exact WuPaper.ClassicalFourthNat.CPay_922
  · exact WuPaper.ClassicalFourthNat.CPay_923
  · exact WuPaper.ClassicalFourthNat.CPay_924
  · exact WuPaper.ClassicalFourthNat.CPay_925
  · exact WuPaper.ClassicalFourthNat.CPay_926
  · exact WuPaper.ClassicalFourthNat.CPay_927
  · exact WuPaper.ClassicalFourthNat.CPay_928
  · exact WuPaper.ClassicalFourthNat.CPay_929
  · exact WuPaper.ClassicalFourthNat.CPay_930
  · exact WuPaper.ClassicalFourthNat.CPay_931
  · exact WuPaper.ClassicalFourthNat.CPay_932
  · exact WuPaper.ClassicalFourthNat.CPay_933
  · exact WuPaper.ClassicalFourthNat.CPay_934
  · exact WuPaper.ClassicalFourthNat.CPay_935
  · exact WuPaper.ClassicalFourthNat.CPay_936
  · exact WuPaper.ClassicalFourthNat.CPay_937
  · exact WuPaper.ClassicalFourthNat.CPay_938
  · exact WuPaper.ClassicalFourthNat.CPay_939
  · exact WuPaper.ClassicalFourthNat.CPay_940
  · exact WuPaper.ClassicalFourthNat.CPay_941
  · exact WuPaper.ClassicalFourthNat.CPay_942
  · exact WuPaper.ClassicalFourthNat.CPay_943
  · exact WuPaper.ClassicalFourthNat.CPay_944
  · exact WuPaper.ClassicalFourthNat.CPay_945
  · exact WuPaper.ClassicalFourthNat.CPay_946
  · exact WuPaper.ClassicalFourthNat.CPay_947
  · exact WuPaper.ClassicalFourthNat.CPay_948
  · exact WuPaper.ClassicalFourthNat.CPay_949
  · exact WuPaper.ClassicalFourthNat.CPay_950
  · exact WuPaper.ClassicalFourthNat.CPay_951
  · exact WuPaper.ClassicalFourthNat.CPay_952
  · exact WuPaper.ClassicalFourthNat.CPay_953
  · exact WuPaper.ClassicalFourthNat.CPay_954
  · exact WuPaper.ClassicalFourthNat.CPay_955
  · exact WuPaper.ClassicalFourthNat.CPay_956
  · exact WuPaper.ClassicalFourthNat.CPay_957
  · exact WuPaper.ClassicalFourthNat.CPay_958
  · exact WuPaper.ClassicalFourthNat.CPay_959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_014
