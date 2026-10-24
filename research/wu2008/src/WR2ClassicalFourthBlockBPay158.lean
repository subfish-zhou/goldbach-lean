import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay158
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_158 (j : Fin 64) (hj : 64*158+j.val < 10540) :
    BPay (64*158+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10112
  · exact WuPaper.ClassicalFourthNat.BPay_10113
  · exact WuPaper.ClassicalFourthNat.BPay_10114
  · exact WuPaper.ClassicalFourthNat.BPay_10115
  · exact WuPaper.ClassicalFourthNat.BPay_10116
  · exact WuPaper.ClassicalFourthNat.BPay_10117
  · exact WuPaper.ClassicalFourthNat.BPay_10118
  · exact WuPaper.ClassicalFourthNat.BPay_10119
  · exact WuPaper.ClassicalFourthNat.BPay_10120
  · exact WuPaper.ClassicalFourthNat.BPay_10121
  · exact WuPaper.ClassicalFourthNat.BPay_10122
  · exact WuPaper.ClassicalFourthNat.BPay_10123
  · exact WuPaper.ClassicalFourthNat.BPay_10124
  · exact WuPaper.ClassicalFourthNat.BPay_10125
  · exact WuPaper.ClassicalFourthNat.BPay_10126
  · exact WuPaper.ClassicalFourthNat.BPay_10127
  · exact WuPaper.ClassicalFourthNat.BPay_10128
  · exact WuPaper.ClassicalFourthNat.BPay_10129
  · exact WuPaper.ClassicalFourthNat.BPay_10130
  · exact WuPaper.ClassicalFourthNat.BPay_10131
  · exact WuPaper.ClassicalFourthNat.BPay_10132
  · exact WuPaper.ClassicalFourthNat.BPay_10133
  · exact WuPaper.ClassicalFourthNat.BPay_10134
  · exact WuPaper.ClassicalFourthNat.BPay_10135
  · exact WuPaper.ClassicalFourthNat.BPay_10136
  · exact WuPaper.ClassicalFourthNat.BPay_10137
  · exact WuPaper.ClassicalFourthNat.BPay_10138
  · exact WuPaper.ClassicalFourthNat.BPay_10139
  · exact WuPaper.ClassicalFourthNat.BPay_10140
  · exact WuPaper.ClassicalFourthNat.BPay_10141
  · exact WuPaper.ClassicalFourthNat.BPay_10142
  · exact WuPaper.ClassicalFourthNat.BPay_10143
  · exact WuPaper.ClassicalFourthNat.BPay_10144
  · exact WuPaper.ClassicalFourthNat.BPay_10145
  · exact WuPaper.ClassicalFourthNat.BPay_10146
  · exact WuPaper.ClassicalFourthNat.BPay_10147
  · exact WuPaper.ClassicalFourthNat.BPay_10148
  · exact WuPaper.ClassicalFourthNat.BPay_10149
  · exact WuPaper.ClassicalFourthNat.BPay_10150
  · exact WuPaper.ClassicalFourthNat.BPay_10151
  · exact WuPaper.ClassicalFourthNat.BPay_10152
  · exact WuPaper.ClassicalFourthNat.BPay_10153
  · exact WuPaper.ClassicalFourthNat.BPay_10154
  · exact WuPaper.ClassicalFourthNat.BPay_10155
  · exact WuPaper.ClassicalFourthNat.BPay_10156
  · exact WuPaper.ClassicalFourthNat.BPay_10157
  · exact WuPaper.ClassicalFourthNat.BPay_10158
  · exact WuPaper.ClassicalFourthNat.BPay_10159
  · exact WuPaper.ClassicalFourthNat.BPay_10160
  · exact WuPaper.ClassicalFourthNat.BPay_10161
  · exact WuPaper.ClassicalFourthNat.BPay_10162
  · exact WuPaper.ClassicalFourthNat.BPay_10163
  · exact WuPaper.ClassicalFourthNat.BPay_10164
  · exact WuPaper.ClassicalFourthNat.BPay_10165
  · exact WuPaper.ClassicalFourthNat.BPay_10166
  · exact WuPaper.ClassicalFourthNat.BPay_10167
  · exact WuPaper.ClassicalFourthNat.BPay_10168
  · exact WuPaper.ClassicalFourthNat.BPay_10169
  · exact WuPaper.ClassicalFourthNat.BPay_10170
  · exact WuPaper.ClassicalFourthNat.BPay_10171
  · exact WuPaper.ClassicalFourthNat.BPay_10172
  · exact WuPaper.ClassicalFourthNat.BPay_10173
  · exact WuPaper.ClassicalFourthNat.BPay_10174
  · exact WuPaper.ClassicalFourthNat.BPay_10175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_158
