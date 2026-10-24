import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay064
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_064 (j : Fin 64) (hj : 64*64+j.val < 10540) :
    BPay (64*64+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4096
  · exact WuPaper.ClassicalFourthNat.BPay_4097
  · exact WuPaper.ClassicalFourthNat.BPay_4098
  · exact WuPaper.ClassicalFourthNat.BPay_4099
  · exact WuPaper.ClassicalFourthNat.BPay_4100
  · exact WuPaper.ClassicalFourthNat.BPay_4101
  · exact WuPaper.ClassicalFourthNat.BPay_4102
  · exact WuPaper.ClassicalFourthNat.BPay_4103
  · exact WuPaper.ClassicalFourthNat.BPay_4104
  · exact WuPaper.ClassicalFourthNat.BPay_4105
  · exact WuPaper.ClassicalFourthNat.BPay_4106
  · exact WuPaper.ClassicalFourthNat.BPay_4107
  · exact WuPaper.ClassicalFourthNat.BPay_4108
  · exact WuPaper.ClassicalFourthNat.BPay_4109
  · exact WuPaper.ClassicalFourthNat.BPay_4110
  · exact WuPaper.ClassicalFourthNat.BPay_4111
  · exact WuPaper.ClassicalFourthNat.BPay_4112
  · exact WuPaper.ClassicalFourthNat.BPay_4113
  · exact WuPaper.ClassicalFourthNat.BPay_4114
  · exact WuPaper.ClassicalFourthNat.BPay_4115
  · exact WuPaper.ClassicalFourthNat.BPay_4116
  · exact WuPaper.ClassicalFourthNat.BPay_4117
  · exact WuPaper.ClassicalFourthNat.BPay_4118
  · exact WuPaper.ClassicalFourthNat.BPay_4119
  · exact WuPaper.ClassicalFourthNat.BPay_4120
  · exact WuPaper.ClassicalFourthNat.BPay_4121
  · exact WuPaper.ClassicalFourthNat.BPay_4122
  · exact WuPaper.ClassicalFourthNat.BPay_4123
  · exact WuPaper.ClassicalFourthNat.BPay_4124
  · exact WuPaper.ClassicalFourthNat.BPay_4125
  · exact WuPaper.ClassicalFourthNat.BPay_4126
  · exact WuPaper.ClassicalFourthNat.BPay_4127
  · exact WuPaper.ClassicalFourthNat.BPay_4128
  · exact WuPaper.ClassicalFourthNat.BPay_4129
  · exact WuPaper.ClassicalFourthNat.BPay_4130
  · exact WuPaper.ClassicalFourthNat.BPay_4131
  · exact WuPaper.ClassicalFourthNat.BPay_4132
  · exact WuPaper.ClassicalFourthNat.BPay_4133
  · exact WuPaper.ClassicalFourthNat.BPay_4134
  · exact WuPaper.ClassicalFourthNat.BPay_4135
  · exact WuPaper.ClassicalFourthNat.BPay_4136
  · exact WuPaper.ClassicalFourthNat.BPay_4137
  · exact WuPaper.ClassicalFourthNat.BPay_4138
  · exact WuPaper.ClassicalFourthNat.BPay_4139
  · exact WuPaper.ClassicalFourthNat.BPay_4140
  · exact WuPaper.ClassicalFourthNat.BPay_4141
  · exact WuPaper.ClassicalFourthNat.BPay_4142
  · exact WuPaper.ClassicalFourthNat.BPay_4143
  · exact WuPaper.ClassicalFourthNat.BPay_4144
  · exact WuPaper.ClassicalFourthNat.BPay_4145
  · exact WuPaper.ClassicalFourthNat.BPay_4146
  · exact WuPaper.ClassicalFourthNat.BPay_4147
  · exact WuPaper.ClassicalFourthNat.BPay_4148
  · exact WuPaper.ClassicalFourthNat.BPay_4149
  · exact WuPaper.ClassicalFourthNat.BPay_4150
  · exact WuPaper.ClassicalFourthNat.BPay_4151
  · exact WuPaper.ClassicalFourthNat.BPay_4152
  · exact WuPaper.ClassicalFourthNat.BPay_4153
  · exact WuPaper.ClassicalFourthNat.BPay_4154
  · exact WuPaper.ClassicalFourthNat.BPay_4155
  · exact WuPaper.ClassicalFourthNat.BPay_4156
  · exact WuPaper.ClassicalFourthNat.BPay_4157
  · exact WuPaper.ClassicalFourthNat.BPay_4158
  · exact WuPaper.ClassicalFourthNat.BPay_4159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_064
