import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay062
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_062 (j : Fin 64) (hj : 64*62+j.val < 10540) :
    BPay (64*62+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3968
  · exact WuPaper.ClassicalFourthNat.BPay_3969
  · exact WuPaper.ClassicalFourthNat.BPay_3970
  · exact WuPaper.ClassicalFourthNat.BPay_3971
  · exact WuPaper.ClassicalFourthNat.BPay_3972
  · exact WuPaper.ClassicalFourthNat.BPay_3973
  · exact WuPaper.ClassicalFourthNat.BPay_3974
  · exact WuPaper.ClassicalFourthNat.BPay_3975
  · exact WuPaper.ClassicalFourthNat.BPay_3976
  · exact WuPaper.ClassicalFourthNat.BPay_3977
  · exact WuPaper.ClassicalFourthNat.BPay_3978
  · exact WuPaper.ClassicalFourthNat.BPay_3979
  · exact WuPaper.ClassicalFourthNat.BPay_3980
  · exact WuPaper.ClassicalFourthNat.BPay_3981
  · exact WuPaper.ClassicalFourthNat.BPay_3982
  · exact WuPaper.ClassicalFourthNat.BPay_3983
  · exact WuPaper.ClassicalFourthNat.BPay_3984
  · exact WuPaper.ClassicalFourthNat.BPay_3985
  · exact WuPaper.ClassicalFourthNat.BPay_3986
  · exact WuPaper.ClassicalFourthNat.BPay_3987
  · exact WuPaper.ClassicalFourthNat.BPay_3988
  · exact WuPaper.ClassicalFourthNat.BPay_3989
  · exact WuPaper.ClassicalFourthNat.BPay_3990
  · exact WuPaper.ClassicalFourthNat.BPay_3991
  · exact WuPaper.ClassicalFourthNat.BPay_3992
  · exact WuPaper.ClassicalFourthNat.BPay_3993
  · exact WuPaper.ClassicalFourthNat.BPay_3994
  · exact WuPaper.ClassicalFourthNat.BPay_3995
  · exact WuPaper.ClassicalFourthNat.BPay_3996
  · exact WuPaper.ClassicalFourthNat.BPay_3997
  · exact WuPaper.ClassicalFourthNat.BPay_3998
  · exact WuPaper.ClassicalFourthNat.BPay_3999
  · exact WuPaper.ClassicalFourthNat.BPay_4000
  · exact WuPaper.ClassicalFourthNat.BPay_4001
  · exact WuPaper.ClassicalFourthNat.BPay_4002
  · exact WuPaper.ClassicalFourthNat.BPay_4003
  · exact WuPaper.ClassicalFourthNat.BPay_4004
  · exact WuPaper.ClassicalFourthNat.BPay_4005
  · exact WuPaper.ClassicalFourthNat.BPay_4006
  · exact WuPaper.ClassicalFourthNat.BPay_4007
  · exact WuPaper.ClassicalFourthNat.BPay_4008
  · exact WuPaper.ClassicalFourthNat.BPay_4009
  · exact WuPaper.ClassicalFourthNat.BPay_4010
  · exact WuPaper.ClassicalFourthNat.BPay_4011
  · exact WuPaper.ClassicalFourthNat.BPay_4012
  · exact WuPaper.ClassicalFourthNat.BPay_4013
  · exact WuPaper.ClassicalFourthNat.BPay_4014
  · exact WuPaper.ClassicalFourthNat.BPay_4015
  · exact WuPaper.ClassicalFourthNat.BPay_4016
  · exact WuPaper.ClassicalFourthNat.BPay_4017
  · exact WuPaper.ClassicalFourthNat.BPay_4018
  · exact WuPaper.ClassicalFourthNat.BPay_4019
  · exact WuPaper.ClassicalFourthNat.BPay_4020
  · exact WuPaper.ClassicalFourthNat.BPay_4021
  · exact WuPaper.ClassicalFourthNat.BPay_4022
  · exact WuPaper.ClassicalFourthNat.BPay_4023
  · exact WuPaper.ClassicalFourthNat.BPay_4024
  · exact WuPaper.ClassicalFourthNat.BPay_4025
  · exact WuPaper.ClassicalFourthNat.BPay_4026
  · exact WuPaper.ClassicalFourthNat.BPay_4027
  · exact WuPaper.ClassicalFourthNat.BPay_4028
  · exact WuPaper.ClassicalFourthNat.BPay_4029
  · exact WuPaper.ClassicalFourthNat.BPay_4030
  · exact WuPaper.ClassicalFourthNat.BPay_4031
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_062
