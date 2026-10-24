import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint125
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_125 (j : Fin 64) (hj : 64*125+j.val < 10541) :
    OuterPoint (64*125+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8000
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8001
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8002
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8003
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8004
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8005
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8006
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8007
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8008
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8009
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8010
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8011
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8012
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8013
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8014
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8015
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8016
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8017
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8018
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8019
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8020
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8021
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8022
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8023
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8024
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8025
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8026
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8027
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8028
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8029
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8030
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8031
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8032
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8033
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8034
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8035
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8036
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8037
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8038
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8039
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8040
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8041
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8042
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8043
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8044
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8045
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8046
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8047
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8048
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8049
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8050
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8051
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8052
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8053
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8054
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8055
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8056
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8057
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8058
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8059
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8060
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8061
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8062
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_125
