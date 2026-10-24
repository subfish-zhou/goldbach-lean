import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay093
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_093 (j : Fin 64) (hj : 64*93+j.val < 10540) :
    BPay (64*93+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5952
  · exact WuPaper.ClassicalFourthNat.BPay_5953
  · exact WuPaper.ClassicalFourthNat.BPay_5954
  · exact WuPaper.ClassicalFourthNat.BPay_5955
  · exact WuPaper.ClassicalFourthNat.BPay_5956
  · exact WuPaper.ClassicalFourthNat.BPay_5957
  · exact WuPaper.ClassicalFourthNat.BPay_5958
  · exact WuPaper.ClassicalFourthNat.BPay_5959
  · exact WuPaper.ClassicalFourthNat.BPay_5960
  · exact WuPaper.ClassicalFourthNat.BPay_5961
  · exact WuPaper.ClassicalFourthNat.BPay_5962
  · exact WuPaper.ClassicalFourthNat.BPay_5963
  · exact WuPaper.ClassicalFourthNat.BPay_5964
  · exact WuPaper.ClassicalFourthNat.BPay_5965
  · exact WuPaper.ClassicalFourthNat.BPay_5966
  · exact WuPaper.ClassicalFourthNat.BPay_5967
  · exact WuPaper.ClassicalFourthNat.BPay_5968
  · exact WuPaper.ClassicalFourthNat.BPay_5969
  · exact WuPaper.ClassicalFourthNat.BPay_5970
  · exact WuPaper.ClassicalFourthNat.BPay_5971
  · exact WuPaper.ClassicalFourthNat.BPay_5972
  · exact WuPaper.ClassicalFourthNat.BPay_5973
  · exact WuPaper.ClassicalFourthNat.BPay_5974
  · exact WuPaper.ClassicalFourthNat.BPay_5975
  · exact WuPaper.ClassicalFourthNat.BPay_5976
  · exact WuPaper.ClassicalFourthNat.BPay_5977
  · exact WuPaper.ClassicalFourthNat.BPay_5978
  · exact WuPaper.ClassicalFourthNat.BPay_5979
  · exact WuPaper.ClassicalFourthNat.BPay_5980
  · exact WuPaper.ClassicalFourthNat.BPay_5981
  · exact WuPaper.ClassicalFourthNat.BPay_5982
  · exact WuPaper.ClassicalFourthNat.BPay_5983
  · exact WuPaper.ClassicalFourthNat.BPay_5984
  · exact WuPaper.ClassicalFourthNat.BPay_5985
  · exact WuPaper.ClassicalFourthNat.BPay_5986
  · exact WuPaper.ClassicalFourthNat.BPay_5987
  · exact WuPaper.ClassicalFourthNat.BPay_5988
  · exact WuPaper.ClassicalFourthNat.BPay_5989
  · exact WuPaper.ClassicalFourthNat.BPay_5990
  · exact WuPaper.ClassicalFourthNat.BPay_5991
  · exact WuPaper.ClassicalFourthNat.BPay_5992
  · exact WuPaper.ClassicalFourthNat.BPay_5993
  · exact WuPaper.ClassicalFourthNat.BPay_5994
  · exact WuPaper.ClassicalFourthNat.BPay_5995
  · exact WuPaper.ClassicalFourthNat.BPay_5996
  · exact WuPaper.ClassicalFourthNat.BPay_5997
  · exact WuPaper.ClassicalFourthNat.BPay_5998
  · exact WuPaper.ClassicalFourthNat.BPay_5999
  · exact WuPaper.ClassicalFourthNat.BPay_6000
  · exact WuPaper.ClassicalFourthNat.BPay_6001
  · exact WuPaper.ClassicalFourthNat.BPay_6002
  · exact WuPaper.ClassicalFourthNat.BPay_6003
  · exact WuPaper.ClassicalFourthNat.BPay_6004
  · exact WuPaper.ClassicalFourthNat.BPay_6005
  · exact WuPaper.ClassicalFourthNat.BPay_6006
  · exact WuPaper.ClassicalFourthNat.BPay_6007
  · exact WuPaper.ClassicalFourthNat.BPay_6008
  · exact WuPaper.ClassicalFourthNat.BPay_6009
  · exact WuPaper.ClassicalFourthNat.BPay_6010
  · exact WuPaper.ClassicalFourthNat.BPay_6011
  · exact WuPaper.ClassicalFourthNat.BPay_6012
  · exact WuPaper.ClassicalFourthNat.BPay_6013
  · exact WuPaper.ClassicalFourthNat.BPay_6014
  · exact WuPaper.ClassicalFourthNat.BPay_6015
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_093
