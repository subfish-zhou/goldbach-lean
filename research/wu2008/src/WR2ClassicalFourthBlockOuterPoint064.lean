import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint064
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_064 (j : Fin 64) (hj : 64*64+j.val < 10541) :
    OuterPoint (64*64+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4096
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4097
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4098
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4099
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4100
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4101
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4102
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4103
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4104
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4105
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4106
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4107
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4108
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4109
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4110
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4111
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4112
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4113
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4114
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4115
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4116
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4117
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4118
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4119
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4120
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4121
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4122
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4123
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4124
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4125
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4126
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4127
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4128
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4129
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4130
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4131
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4132
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4133
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4134
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4135
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4136
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4137
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4138
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4139
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4140
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4141
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4142
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4143
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4144
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4145
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4146
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4147
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4148
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4149
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4150
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4151
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4152
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4153
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4154
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4155
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4156
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4157
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4158
  · exact WuPaper.ClassicalFourthNat.OuterPoint_4159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_064
