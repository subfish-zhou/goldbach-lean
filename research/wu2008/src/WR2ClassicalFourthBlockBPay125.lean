import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay125
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_125 (j : Fin 64) (hj : 64*125+j.val < 10540) :
    BPay (64*125+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8000
  · exact WuPaper.ClassicalFourthNat.BPay_8001
  · exact WuPaper.ClassicalFourthNat.BPay_8002
  · exact WuPaper.ClassicalFourthNat.BPay_8003
  · exact WuPaper.ClassicalFourthNat.BPay_8004
  · exact WuPaper.ClassicalFourthNat.BPay_8005
  · exact WuPaper.ClassicalFourthNat.BPay_8006
  · exact WuPaper.ClassicalFourthNat.BPay_8007
  · exact WuPaper.ClassicalFourthNat.BPay_8008
  · exact WuPaper.ClassicalFourthNat.BPay_8009
  · exact WuPaper.ClassicalFourthNat.BPay_8010
  · exact WuPaper.ClassicalFourthNat.BPay_8011
  · exact WuPaper.ClassicalFourthNat.BPay_8012
  · exact WuPaper.ClassicalFourthNat.BPay_8013
  · exact WuPaper.ClassicalFourthNat.BPay_8014
  · exact WuPaper.ClassicalFourthNat.BPay_8015
  · exact WuPaper.ClassicalFourthNat.BPay_8016
  · exact WuPaper.ClassicalFourthNat.BPay_8017
  · exact WuPaper.ClassicalFourthNat.BPay_8018
  · exact WuPaper.ClassicalFourthNat.BPay_8019
  · exact WuPaper.ClassicalFourthNat.BPay_8020
  · exact WuPaper.ClassicalFourthNat.BPay_8021
  · exact WuPaper.ClassicalFourthNat.BPay_8022
  · exact WuPaper.ClassicalFourthNat.BPay_8023
  · exact WuPaper.ClassicalFourthNat.BPay_8024
  · exact WuPaper.ClassicalFourthNat.BPay_8025
  · exact WuPaper.ClassicalFourthNat.BPay_8026
  · exact WuPaper.ClassicalFourthNat.BPay_8027
  · exact WuPaper.ClassicalFourthNat.BPay_8028
  · exact WuPaper.ClassicalFourthNat.BPay_8029
  · exact WuPaper.ClassicalFourthNat.BPay_8030
  · exact WuPaper.ClassicalFourthNat.BPay_8031
  · exact WuPaper.ClassicalFourthNat.BPay_8032
  · exact WuPaper.ClassicalFourthNat.BPay_8033
  · exact WuPaper.ClassicalFourthNat.BPay_8034
  · exact WuPaper.ClassicalFourthNat.BPay_8035
  · exact WuPaper.ClassicalFourthNat.BPay_8036
  · exact WuPaper.ClassicalFourthNat.BPay_8037
  · exact WuPaper.ClassicalFourthNat.BPay_8038
  · exact WuPaper.ClassicalFourthNat.BPay_8039
  · exact WuPaper.ClassicalFourthNat.BPay_8040
  · exact WuPaper.ClassicalFourthNat.BPay_8041
  · exact WuPaper.ClassicalFourthNat.BPay_8042
  · exact WuPaper.ClassicalFourthNat.BPay_8043
  · exact WuPaper.ClassicalFourthNat.BPay_8044
  · exact WuPaper.ClassicalFourthNat.BPay_8045
  · exact WuPaper.ClassicalFourthNat.BPay_8046
  · exact WuPaper.ClassicalFourthNat.BPay_8047
  · exact WuPaper.ClassicalFourthNat.BPay_8048
  · exact WuPaper.ClassicalFourthNat.BPay_8049
  · exact WuPaper.ClassicalFourthNat.BPay_8050
  · exact WuPaper.ClassicalFourthNat.BPay_8051
  · exact WuPaper.ClassicalFourthNat.BPay_8052
  · exact WuPaper.ClassicalFourthNat.BPay_8053
  · exact WuPaper.ClassicalFourthNat.BPay_8054
  · exact WuPaper.ClassicalFourthNat.BPay_8055
  · exact WuPaper.ClassicalFourthNat.BPay_8056
  · exact WuPaper.ClassicalFourthNat.BPay_8057
  · exact WuPaper.ClassicalFourthNat.BPay_8058
  · exact WuPaper.ClassicalFourthNat.BPay_8059
  · exact WuPaper.ClassicalFourthNat.BPay_8060
  · exact WuPaper.ClassicalFourthNat.BPay_8061
  · exact WuPaper.ClassicalFourthNat.BPay_8062
  · exact WuPaper.ClassicalFourthNat.BPay_8063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_125
