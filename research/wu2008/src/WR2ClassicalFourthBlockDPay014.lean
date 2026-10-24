import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay014
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_014 (j : Fin 64) (hj : 64*14+j.val < 2540) :
    DPay (64*14+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_896
  · exact WuPaper.ClassicalFourthNat.DPay_897
  · exact WuPaper.ClassicalFourthNat.DPay_898
  · exact WuPaper.ClassicalFourthNat.DPay_899
  · exact WuPaper.ClassicalFourthNat.DPay_900
  · exact WuPaper.ClassicalFourthNat.DPay_901
  · exact WuPaper.ClassicalFourthNat.DPay_902
  · exact WuPaper.ClassicalFourthNat.DPay_903
  · exact WuPaper.ClassicalFourthNat.DPay_904
  · exact WuPaper.ClassicalFourthNat.DPay_905
  · exact WuPaper.ClassicalFourthNat.DPay_906
  · exact WuPaper.ClassicalFourthNat.DPay_907
  · exact WuPaper.ClassicalFourthNat.DPay_908
  · exact WuPaper.ClassicalFourthNat.DPay_909
  · exact WuPaper.ClassicalFourthNat.DPay_910
  · exact WuPaper.ClassicalFourthNat.DPay_911
  · exact WuPaper.ClassicalFourthNat.DPay_912
  · exact WuPaper.ClassicalFourthNat.DPay_913
  · exact WuPaper.ClassicalFourthNat.DPay_914
  · exact WuPaper.ClassicalFourthNat.DPay_915
  · exact WuPaper.ClassicalFourthNat.DPay_916
  · exact WuPaper.ClassicalFourthNat.DPay_917
  · exact WuPaper.ClassicalFourthNat.DPay_918
  · exact WuPaper.ClassicalFourthNat.DPay_919
  · exact WuPaper.ClassicalFourthNat.DPay_920
  · exact WuPaper.ClassicalFourthNat.DPay_921
  · exact WuPaper.ClassicalFourthNat.DPay_922
  · exact WuPaper.ClassicalFourthNat.DPay_923
  · exact WuPaper.ClassicalFourthNat.DPay_924
  · exact WuPaper.ClassicalFourthNat.DPay_925
  · exact WuPaper.ClassicalFourthNat.DPay_926
  · exact WuPaper.ClassicalFourthNat.DPay_927
  · exact WuPaper.ClassicalFourthNat.DPay_928
  · exact WuPaper.ClassicalFourthNat.DPay_929
  · exact WuPaper.ClassicalFourthNat.DPay_930
  · exact WuPaper.ClassicalFourthNat.DPay_931
  · exact WuPaper.ClassicalFourthNat.DPay_932
  · exact WuPaper.ClassicalFourthNat.DPay_933
  · exact WuPaper.ClassicalFourthNat.DPay_934
  · exact WuPaper.ClassicalFourthNat.DPay_935
  · exact WuPaper.ClassicalFourthNat.DPay_936
  · exact WuPaper.ClassicalFourthNat.DPay_937
  · exact WuPaper.ClassicalFourthNat.DPay_938
  · exact WuPaper.ClassicalFourthNat.DPay_939
  · exact WuPaper.ClassicalFourthNat.DPay_940
  · exact WuPaper.ClassicalFourthNat.DPay_941
  · exact WuPaper.ClassicalFourthNat.DPay_942
  · exact WuPaper.ClassicalFourthNat.DPay_943
  · exact WuPaper.ClassicalFourthNat.DPay_944
  · exact WuPaper.ClassicalFourthNat.DPay_945
  · exact WuPaper.ClassicalFourthNat.DPay_946
  · exact WuPaper.ClassicalFourthNat.DPay_947
  · exact WuPaper.ClassicalFourthNat.DPay_948
  · exact WuPaper.ClassicalFourthNat.DPay_949
  · exact WuPaper.ClassicalFourthNat.DPay_950
  · exact WuPaper.ClassicalFourthNat.DPay_951
  · exact WuPaper.ClassicalFourthNat.DPay_952
  · exact WuPaper.ClassicalFourthNat.DPay_953
  · exact WuPaper.ClassicalFourthNat.DPay_954
  · exact WuPaper.ClassicalFourthNat.DPay_955
  · exact WuPaper.ClassicalFourthNat.DPay_956
  · exact WuPaper.ClassicalFourthNat.DPay_957
  · exact WuPaper.ClassicalFourthNat.DPay_958
  · exact WuPaper.ClassicalFourthNat.DPay_959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_014
