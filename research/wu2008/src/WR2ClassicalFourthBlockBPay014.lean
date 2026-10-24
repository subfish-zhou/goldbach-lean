import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay014
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_014 (j : Fin 64) (hj : 64*14+j.val < 10540) :
    BPay (64*14+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_896
  · exact WuPaper.ClassicalFourthNat.BPay_897
  · exact WuPaper.ClassicalFourthNat.BPay_898
  · exact WuPaper.ClassicalFourthNat.BPay_899
  · exact WuPaper.ClassicalFourthNat.BPay_900
  · exact WuPaper.ClassicalFourthNat.BPay_901
  · exact WuPaper.ClassicalFourthNat.BPay_902
  · exact WuPaper.ClassicalFourthNat.BPay_903
  · exact WuPaper.ClassicalFourthNat.BPay_904
  · exact WuPaper.ClassicalFourthNat.BPay_905
  · exact WuPaper.ClassicalFourthNat.BPay_906
  · exact WuPaper.ClassicalFourthNat.BPay_907
  · exact WuPaper.ClassicalFourthNat.BPay_908
  · exact WuPaper.ClassicalFourthNat.BPay_909
  · exact WuPaper.ClassicalFourthNat.BPay_910
  · exact WuPaper.ClassicalFourthNat.BPay_911
  · exact WuPaper.ClassicalFourthNat.BPay_912
  · exact WuPaper.ClassicalFourthNat.BPay_913
  · exact WuPaper.ClassicalFourthNat.BPay_914
  · exact WuPaper.ClassicalFourthNat.BPay_915
  · exact WuPaper.ClassicalFourthNat.BPay_916
  · exact WuPaper.ClassicalFourthNat.BPay_917
  · exact WuPaper.ClassicalFourthNat.BPay_918
  · exact WuPaper.ClassicalFourthNat.BPay_919
  · exact WuPaper.ClassicalFourthNat.BPay_920
  · exact WuPaper.ClassicalFourthNat.BPay_921
  · exact WuPaper.ClassicalFourthNat.BPay_922
  · exact WuPaper.ClassicalFourthNat.BPay_923
  · exact WuPaper.ClassicalFourthNat.BPay_924
  · exact WuPaper.ClassicalFourthNat.BPay_925
  · exact WuPaper.ClassicalFourthNat.BPay_926
  · exact WuPaper.ClassicalFourthNat.BPay_927
  · exact WuPaper.ClassicalFourthNat.BPay_928
  · exact WuPaper.ClassicalFourthNat.BPay_929
  · exact WuPaper.ClassicalFourthNat.BPay_930
  · exact WuPaper.ClassicalFourthNat.BPay_931
  · exact WuPaper.ClassicalFourthNat.BPay_932
  · exact WuPaper.ClassicalFourthNat.BPay_933
  · exact WuPaper.ClassicalFourthNat.BPay_934
  · exact WuPaper.ClassicalFourthNat.BPay_935
  · exact WuPaper.ClassicalFourthNat.BPay_936
  · exact WuPaper.ClassicalFourthNat.BPay_937
  · exact WuPaper.ClassicalFourthNat.BPay_938
  · exact WuPaper.ClassicalFourthNat.BPay_939
  · exact WuPaper.ClassicalFourthNat.BPay_940
  · exact WuPaper.ClassicalFourthNat.BPay_941
  · exact WuPaper.ClassicalFourthNat.BPay_942
  · exact WuPaper.ClassicalFourthNat.BPay_943
  · exact WuPaper.ClassicalFourthNat.BPay_944
  · exact WuPaper.ClassicalFourthNat.BPay_945
  · exact WuPaper.ClassicalFourthNat.BPay_946
  · exact WuPaper.ClassicalFourthNat.BPay_947
  · exact WuPaper.ClassicalFourthNat.BPay_948
  · exact WuPaper.ClassicalFourthNat.BPay_949
  · exact WuPaper.ClassicalFourthNat.BPay_950
  · exact WuPaper.ClassicalFourthNat.BPay_951
  · exact WuPaper.ClassicalFourthNat.BPay_952
  · exact WuPaper.ClassicalFourthNat.BPay_953
  · exact WuPaper.ClassicalFourthNat.BPay_954
  · exact WuPaper.ClassicalFourthNat.BPay_955
  · exact WuPaper.ClassicalFourthNat.BPay_956
  · exact WuPaper.ClassicalFourthNat.BPay_957
  · exact WuPaper.ClassicalFourthNat.BPay_958
  · exact WuPaper.ClassicalFourthNat.BPay_959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_014
