import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay063
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_063 (j : Fin 64) (hj : 64*63+j.val < 10540) :
    OuterPay (64*63+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_4032
  · exact WuPaper.ClassicalFourthNat.outerPay_4033
  · exact WuPaper.ClassicalFourthNat.outerPay_4034
  · exact WuPaper.ClassicalFourthNat.outerPay_4035
  · exact WuPaper.ClassicalFourthNat.outerPay_4036
  · exact WuPaper.ClassicalFourthNat.outerPay_4037
  · exact WuPaper.ClassicalFourthNat.outerPay_4038
  · exact WuPaper.ClassicalFourthNat.outerPay_4039
  · exact WuPaper.ClassicalFourthNat.outerPay_4040
  · exact WuPaper.ClassicalFourthNat.outerPay_4041
  · exact WuPaper.ClassicalFourthNat.outerPay_4042
  · exact WuPaper.ClassicalFourthNat.outerPay_4043
  · exact WuPaper.ClassicalFourthNat.outerPay_4044
  · exact WuPaper.ClassicalFourthNat.outerPay_4045
  · exact WuPaper.ClassicalFourthNat.outerPay_4046
  · exact WuPaper.ClassicalFourthNat.outerPay_4047
  · exact WuPaper.ClassicalFourthNat.outerPay_4048
  · exact WuPaper.ClassicalFourthNat.outerPay_4049
  · exact WuPaper.ClassicalFourthNat.outerPay_4050
  · exact WuPaper.ClassicalFourthNat.outerPay_4051
  · exact WuPaper.ClassicalFourthNat.outerPay_4052
  · exact WuPaper.ClassicalFourthNat.outerPay_4053
  · exact WuPaper.ClassicalFourthNat.outerPay_4054
  · exact WuPaper.ClassicalFourthNat.outerPay_4055
  · exact WuPaper.ClassicalFourthNat.outerPay_4056
  · exact WuPaper.ClassicalFourthNat.outerPay_4057
  · exact WuPaper.ClassicalFourthNat.outerPay_4058
  · exact WuPaper.ClassicalFourthNat.outerPay_4059
  · exact WuPaper.ClassicalFourthNat.outerPay_4060
  · exact WuPaper.ClassicalFourthNat.outerPay_4061
  · exact WuPaper.ClassicalFourthNat.outerPay_4062
  · exact WuPaper.ClassicalFourthNat.outerPay_4063
  · exact WuPaper.ClassicalFourthNat.outerPay_4064
  · exact WuPaper.ClassicalFourthNat.outerPay_4065
  · exact WuPaper.ClassicalFourthNat.outerPay_4066
  · exact WuPaper.ClassicalFourthNat.outerPay_4067
  · exact WuPaper.ClassicalFourthNat.outerPay_4068
  · exact WuPaper.ClassicalFourthNat.outerPay_4069
  · exact WuPaper.ClassicalFourthNat.outerPay_4070
  · exact WuPaper.ClassicalFourthNat.outerPay_4071
  · exact WuPaper.ClassicalFourthNat.outerPay_4072
  · exact WuPaper.ClassicalFourthNat.outerPay_4073
  · exact WuPaper.ClassicalFourthNat.outerPay_4074
  · exact WuPaper.ClassicalFourthNat.outerPay_4075
  · exact WuPaper.ClassicalFourthNat.outerPay_4076
  · exact WuPaper.ClassicalFourthNat.outerPay_4077
  · exact WuPaper.ClassicalFourthNat.outerPay_4078
  · exact WuPaper.ClassicalFourthNat.outerPay_4079
  · exact WuPaper.ClassicalFourthNat.outerPay_4080
  · exact WuPaper.ClassicalFourthNat.outerPay_4081
  · exact WuPaper.ClassicalFourthNat.outerPay_4082
  · exact WuPaper.ClassicalFourthNat.outerPay_4083
  · exact WuPaper.ClassicalFourthNat.outerPay_4084
  · exact WuPaper.ClassicalFourthNat.outerPay_4085
  · exact WuPaper.ClassicalFourthNat.outerPay_4086
  · exact WuPaper.ClassicalFourthNat.outerPay_4087
  · exact WuPaper.ClassicalFourthNat.outerPay_4088
  · exact WuPaper.ClassicalFourthNat.outerPay_4089
  · exact WuPaper.ClassicalFourthNat.outerPay_4090
  · exact WuPaper.ClassicalFourthNat.outerPay_4091
  · exact WuPaper.ClassicalFourthNat.outerPay_4092
  · exact WuPaper.ClassicalFourthNat.outerPay_4093
  · exact WuPaper.ClassicalFourthNat.outerPay_4094
  · exact WuPaper.ClassicalFourthNat.outerPay_4095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_063
