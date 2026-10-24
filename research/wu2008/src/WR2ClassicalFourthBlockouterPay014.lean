import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay014
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_014 (j : Fin 64) (hj : 64*14+j.val < 10540) :
    OuterPay (64*14+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_896
  · exact WuPaper.ClassicalFourthNat.outerPay_897
  · exact WuPaper.ClassicalFourthNat.outerPay_898
  · exact WuPaper.ClassicalFourthNat.outerPay_899
  · exact WuPaper.ClassicalFourthNat.outerPay_900
  · exact WuPaper.ClassicalFourthNat.outerPay_901
  · exact WuPaper.ClassicalFourthNat.outerPay_902
  · exact WuPaper.ClassicalFourthNat.outerPay_903
  · exact WuPaper.ClassicalFourthNat.outerPay_904
  · exact WuPaper.ClassicalFourthNat.outerPay_905
  · exact WuPaper.ClassicalFourthNat.outerPay_906
  · exact WuPaper.ClassicalFourthNat.outerPay_907
  · exact WuPaper.ClassicalFourthNat.outerPay_908
  · exact WuPaper.ClassicalFourthNat.outerPay_909
  · exact WuPaper.ClassicalFourthNat.outerPay_910
  · exact WuPaper.ClassicalFourthNat.outerPay_911
  · exact WuPaper.ClassicalFourthNat.outerPay_912
  · exact WuPaper.ClassicalFourthNat.outerPay_913
  · exact WuPaper.ClassicalFourthNat.outerPay_914
  · exact WuPaper.ClassicalFourthNat.outerPay_915
  · exact WuPaper.ClassicalFourthNat.outerPay_916
  · exact WuPaper.ClassicalFourthNat.outerPay_917
  · exact WuPaper.ClassicalFourthNat.outerPay_918
  · exact WuPaper.ClassicalFourthNat.outerPay_919
  · exact WuPaper.ClassicalFourthNat.outerPay_920
  · exact WuPaper.ClassicalFourthNat.outerPay_921
  · exact WuPaper.ClassicalFourthNat.outerPay_922
  · exact WuPaper.ClassicalFourthNat.outerPay_923
  · exact WuPaper.ClassicalFourthNat.outerPay_924
  · exact WuPaper.ClassicalFourthNat.outerPay_925
  · exact WuPaper.ClassicalFourthNat.outerPay_926
  · exact WuPaper.ClassicalFourthNat.outerPay_927
  · exact WuPaper.ClassicalFourthNat.outerPay_928
  · exact WuPaper.ClassicalFourthNat.outerPay_929
  · exact WuPaper.ClassicalFourthNat.outerPay_930
  · exact WuPaper.ClassicalFourthNat.outerPay_931
  · exact WuPaper.ClassicalFourthNat.outerPay_932
  · exact WuPaper.ClassicalFourthNat.outerPay_933
  · exact WuPaper.ClassicalFourthNat.outerPay_934
  · exact WuPaper.ClassicalFourthNat.outerPay_935
  · exact WuPaper.ClassicalFourthNat.outerPay_936
  · exact WuPaper.ClassicalFourthNat.outerPay_937
  · exact WuPaper.ClassicalFourthNat.outerPay_938
  · exact WuPaper.ClassicalFourthNat.outerPay_939
  · exact WuPaper.ClassicalFourthNat.outerPay_940
  · exact WuPaper.ClassicalFourthNat.outerPay_941
  · exact WuPaper.ClassicalFourthNat.outerPay_942
  · exact WuPaper.ClassicalFourthNat.outerPay_943
  · exact WuPaper.ClassicalFourthNat.outerPay_944
  · exact WuPaper.ClassicalFourthNat.outerPay_945
  · exact WuPaper.ClassicalFourthNat.outerPay_946
  · exact WuPaper.ClassicalFourthNat.outerPay_947
  · exact WuPaper.ClassicalFourthNat.outerPay_948
  · exact WuPaper.ClassicalFourthNat.outerPay_949
  · exact WuPaper.ClassicalFourthNat.outerPay_950
  · exact WuPaper.ClassicalFourthNat.outerPay_951
  · exact WuPaper.ClassicalFourthNat.outerPay_952
  · exact WuPaper.ClassicalFourthNat.outerPay_953
  · exact WuPaper.ClassicalFourthNat.outerPay_954
  · exact WuPaper.ClassicalFourthNat.outerPay_955
  · exact WuPaper.ClassicalFourthNat.outerPay_956
  · exact WuPaper.ClassicalFourthNat.outerPay_957
  · exact WuPaper.ClassicalFourthNat.outerPay_958
  · exact WuPaper.ClassicalFourthNat.outerPay_959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_014
