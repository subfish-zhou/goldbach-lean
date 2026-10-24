import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay125
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_125 (j : Fin 64) (hj : 64*125+j.val < 10540) :
    OuterPay (64*125+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8000
  · exact WuPaper.ClassicalFourthNat.outerPay_8001
  · exact WuPaper.ClassicalFourthNat.outerPay_8002
  · exact WuPaper.ClassicalFourthNat.outerPay_8003
  · exact WuPaper.ClassicalFourthNat.outerPay_8004
  · exact WuPaper.ClassicalFourthNat.outerPay_8005
  · exact WuPaper.ClassicalFourthNat.outerPay_8006
  · exact WuPaper.ClassicalFourthNat.outerPay_8007
  · exact WuPaper.ClassicalFourthNat.outerPay_8008
  · exact WuPaper.ClassicalFourthNat.outerPay_8009
  · exact WuPaper.ClassicalFourthNat.outerPay_8010
  · exact WuPaper.ClassicalFourthNat.outerPay_8011
  · exact WuPaper.ClassicalFourthNat.outerPay_8012
  · exact WuPaper.ClassicalFourthNat.outerPay_8013
  · exact WuPaper.ClassicalFourthNat.outerPay_8014
  · exact WuPaper.ClassicalFourthNat.outerPay_8015
  · exact WuPaper.ClassicalFourthNat.outerPay_8016
  · exact WuPaper.ClassicalFourthNat.outerPay_8017
  · exact WuPaper.ClassicalFourthNat.outerPay_8018
  · exact WuPaper.ClassicalFourthNat.outerPay_8019
  · exact WuPaper.ClassicalFourthNat.outerPay_8020
  · exact WuPaper.ClassicalFourthNat.outerPay_8021
  · exact WuPaper.ClassicalFourthNat.outerPay_8022
  · exact WuPaper.ClassicalFourthNat.outerPay_8023
  · exact WuPaper.ClassicalFourthNat.outerPay_8024
  · exact WuPaper.ClassicalFourthNat.outerPay_8025
  · exact WuPaper.ClassicalFourthNat.outerPay_8026
  · exact WuPaper.ClassicalFourthNat.outerPay_8027
  · exact WuPaper.ClassicalFourthNat.outerPay_8028
  · exact WuPaper.ClassicalFourthNat.outerPay_8029
  · exact WuPaper.ClassicalFourthNat.outerPay_8030
  · exact WuPaper.ClassicalFourthNat.outerPay_8031
  · exact WuPaper.ClassicalFourthNat.outerPay_8032
  · exact WuPaper.ClassicalFourthNat.outerPay_8033
  · exact WuPaper.ClassicalFourthNat.outerPay_8034
  · exact WuPaper.ClassicalFourthNat.outerPay_8035
  · exact WuPaper.ClassicalFourthNat.outerPay_8036
  · exact WuPaper.ClassicalFourthNat.outerPay_8037
  · exact WuPaper.ClassicalFourthNat.outerPay_8038
  · exact WuPaper.ClassicalFourthNat.outerPay_8039
  · exact WuPaper.ClassicalFourthNat.outerPay_8040
  · exact WuPaper.ClassicalFourthNat.outerPay_8041
  · exact WuPaper.ClassicalFourthNat.outerPay_8042
  · exact WuPaper.ClassicalFourthNat.outerPay_8043
  · exact WuPaper.ClassicalFourthNat.outerPay_8044
  · exact WuPaper.ClassicalFourthNat.outerPay_8045
  · exact WuPaper.ClassicalFourthNat.outerPay_8046
  · exact WuPaper.ClassicalFourthNat.outerPay_8047
  · exact WuPaper.ClassicalFourthNat.outerPay_8048
  · exact WuPaper.ClassicalFourthNat.outerPay_8049
  · exact WuPaper.ClassicalFourthNat.outerPay_8050
  · exact WuPaper.ClassicalFourthNat.outerPay_8051
  · exact WuPaper.ClassicalFourthNat.outerPay_8052
  · exact WuPaper.ClassicalFourthNat.outerPay_8053
  · exact WuPaper.ClassicalFourthNat.outerPay_8054
  · exact WuPaper.ClassicalFourthNat.outerPay_8055
  · exact WuPaper.ClassicalFourthNat.outerPay_8056
  · exact WuPaper.ClassicalFourthNat.outerPay_8057
  · exact WuPaper.ClassicalFourthNat.outerPay_8058
  · exact WuPaper.ClassicalFourthNat.outerPay_8059
  · exact WuPaper.ClassicalFourthNat.outerPay_8060
  · exact WuPaper.ClassicalFourthNat.outerPay_8061
  · exact WuPaper.ClassicalFourthNat.outerPay_8062
  · exact WuPaper.ClassicalFourthNat.outerPay_8063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_125
