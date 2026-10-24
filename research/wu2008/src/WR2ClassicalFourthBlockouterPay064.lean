import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay064
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_064 (j : Fin 64) (hj : 64*64+j.val < 10540) :
    OuterPay (64*64+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_4096
  · exact WuPaper.ClassicalFourthNat.outerPay_4097
  · exact WuPaper.ClassicalFourthNat.outerPay_4098
  · exact WuPaper.ClassicalFourthNat.outerPay_4099
  · exact WuPaper.ClassicalFourthNat.outerPay_4100
  · exact WuPaper.ClassicalFourthNat.outerPay_4101
  · exact WuPaper.ClassicalFourthNat.outerPay_4102
  · exact WuPaper.ClassicalFourthNat.outerPay_4103
  · exact WuPaper.ClassicalFourthNat.outerPay_4104
  · exact WuPaper.ClassicalFourthNat.outerPay_4105
  · exact WuPaper.ClassicalFourthNat.outerPay_4106
  · exact WuPaper.ClassicalFourthNat.outerPay_4107
  · exact WuPaper.ClassicalFourthNat.outerPay_4108
  · exact WuPaper.ClassicalFourthNat.outerPay_4109
  · exact WuPaper.ClassicalFourthNat.outerPay_4110
  · exact WuPaper.ClassicalFourthNat.outerPay_4111
  · exact WuPaper.ClassicalFourthNat.outerPay_4112
  · exact WuPaper.ClassicalFourthNat.outerPay_4113
  · exact WuPaper.ClassicalFourthNat.outerPay_4114
  · exact WuPaper.ClassicalFourthNat.outerPay_4115
  · exact WuPaper.ClassicalFourthNat.outerPay_4116
  · exact WuPaper.ClassicalFourthNat.outerPay_4117
  · exact WuPaper.ClassicalFourthNat.outerPay_4118
  · exact WuPaper.ClassicalFourthNat.outerPay_4119
  · exact WuPaper.ClassicalFourthNat.outerPay_4120
  · exact WuPaper.ClassicalFourthNat.outerPay_4121
  · exact WuPaper.ClassicalFourthNat.outerPay_4122
  · exact WuPaper.ClassicalFourthNat.outerPay_4123
  · exact WuPaper.ClassicalFourthNat.outerPay_4124
  · exact WuPaper.ClassicalFourthNat.outerPay_4125
  · exact WuPaper.ClassicalFourthNat.outerPay_4126
  · exact WuPaper.ClassicalFourthNat.outerPay_4127
  · exact WuPaper.ClassicalFourthNat.outerPay_4128
  · exact WuPaper.ClassicalFourthNat.outerPay_4129
  · exact WuPaper.ClassicalFourthNat.outerPay_4130
  · exact WuPaper.ClassicalFourthNat.outerPay_4131
  · exact WuPaper.ClassicalFourthNat.outerPay_4132
  · exact WuPaper.ClassicalFourthNat.outerPay_4133
  · exact WuPaper.ClassicalFourthNat.outerPay_4134
  · exact WuPaper.ClassicalFourthNat.outerPay_4135
  · exact WuPaper.ClassicalFourthNat.outerPay_4136
  · exact WuPaper.ClassicalFourthNat.outerPay_4137
  · exact WuPaper.ClassicalFourthNat.outerPay_4138
  · exact WuPaper.ClassicalFourthNat.outerPay_4139
  · exact WuPaper.ClassicalFourthNat.outerPay_4140
  · exact WuPaper.ClassicalFourthNat.outerPay_4141
  · exact WuPaper.ClassicalFourthNat.outerPay_4142
  · exact WuPaper.ClassicalFourthNat.outerPay_4143
  · exact WuPaper.ClassicalFourthNat.outerPay_4144
  · exact WuPaper.ClassicalFourthNat.outerPay_4145
  · exact WuPaper.ClassicalFourthNat.outerPay_4146
  · exact WuPaper.ClassicalFourthNat.outerPay_4147
  · exact WuPaper.ClassicalFourthNat.outerPay_4148
  · exact WuPaper.ClassicalFourthNat.outerPay_4149
  · exact WuPaper.ClassicalFourthNat.outerPay_4150
  · exact WuPaper.ClassicalFourthNat.outerPay_4151
  · exact WuPaper.ClassicalFourthNat.outerPay_4152
  · exact WuPaper.ClassicalFourthNat.outerPay_4153
  · exact WuPaper.ClassicalFourthNat.outerPay_4154
  · exact WuPaper.ClassicalFourthNat.outerPay_4155
  · exact WuPaper.ClassicalFourthNat.outerPay_4156
  · exact WuPaper.ClassicalFourthNat.outerPay_4157
  · exact WuPaper.ClassicalFourthNat.outerPay_4158
  · exact WuPaper.ClassicalFourthNat.outerPay_4159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_064
