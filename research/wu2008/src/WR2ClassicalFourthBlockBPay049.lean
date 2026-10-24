import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay049
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_049 (j : Fin 64) (hj : 64*49+j.val < 10540) :
    BPay (64*49+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3136
  · exact WuPaper.ClassicalFourthNat.BPay_3137
  · exact WuPaper.ClassicalFourthNat.BPay_3138
  · exact WuPaper.ClassicalFourthNat.BPay_3139
  · exact WuPaper.ClassicalFourthNat.BPay_3140
  · exact WuPaper.ClassicalFourthNat.BPay_3141
  · exact WuPaper.ClassicalFourthNat.BPay_3142
  · exact WuPaper.ClassicalFourthNat.BPay_3143
  · exact WuPaper.ClassicalFourthNat.BPay_3144
  · exact WuPaper.ClassicalFourthNat.BPay_3145
  · exact WuPaper.ClassicalFourthNat.BPay_3146
  · exact WuPaper.ClassicalFourthNat.BPay_3147
  · exact WuPaper.ClassicalFourthNat.BPay_3148
  · exact WuPaper.ClassicalFourthNat.BPay_3149
  · exact WuPaper.ClassicalFourthNat.BPay_3150
  · exact WuPaper.ClassicalFourthNat.BPay_3151
  · exact WuPaper.ClassicalFourthNat.BPay_3152
  · exact WuPaper.ClassicalFourthNat.BPay_3153
  · exact WuPaper.ClassicalFourthNat.BPay_3154
  · exact WuPaper.ClassicalFourthNat.BPay_3155
  · exact WuPaper.ClassicalFourthNat.BPay_3156
  · exact WuPaper.ClassicalFourthNat.BPay_3157
  · exact WuPaper.ClassicalFourthNat.BPay_3158
  · exact WuPaper.ClassicalFourthNat.BPay_3159
  · exact WuPaper.ClassicalFourthNat.BPay_3160
  · exact WuPaper.ClassicalFourthNat.BPay_3161
  · exact WuPaper.ClassicalFourthNat.BPay_3162
  · exact WuPaper.ClassicalFourthNat.BPay_3163
  · exact WuPaper.ClassicalFourthNat.BPay_3164
  · exact WuPaper.ClassicalFourthNat.BPay_3165
  · exact WuPaper.ClassicalFourthNat.BPay_3166
  · exact WuPaper.ClassicalFourthNat.BPay_3167
  · exact WuPaper.ClassicalFourthNat.BPay_3168
  · exact WuPaper.ClassicalFourthNat.BPay_3169
  · exact WuPaper.ClassicalFourthNat.BPay_3170
  · exact WuPaper.ClassicalFourthNat.BPay_3171
  · exact WuPaper.ClassicalFourthNat.BPay_3172
  · exact WuPaper.ClassicalFourthNat.BPay_3173
  · exact WuPaper.ClassicalFourthNat.BPay_3174
  · exact WuPaper.ClassicalFourthNat.BPay_3175
  · exact WuPaper.ClassicalFourthNat.BPay_3176
  · exact WuPaper.ClassicalFourthNat.BPay_3177
  · exact WuPaper.ClassicalFourthNat.BPay_3178
  · exact WuPaper.ClassicalFourthNat.BPay_3179
  · exact WuPaper.ClassicalFourthNat.BPay_3180
  · exact WuPaper.ClassicalFourthNat.BPay_3181
  · exact WuPaper.ClassicalFourthNat.BPay_3182
  · exact WuPaper.ClassicalFourthNat.BPay_3183
  · exact WuPaper.ClassicalFourthNat.BPay_3184
  · exact WuPaper.ClassicalFourthNat.BPay_3185
  · exact WuPaper.ClassicalFourthNat.BPay_3186
  · exact WuPaper.ClassicalFourthNat.BPay_3187
  · exact WuPaper.ClassicalFourthNat.BPay_3188
  · exact WuPaper.ClassicalFourthNat.BPay_3189
  · exact WuPaper.ClassicalFourthNat.BPay_3190
  · exact WuPaper.ClassicalFourthNat.BPay_3191
  · exact WuPaper.ClassicalFourthNat.BPay_3192
  · exact WuPaper.ClassicalFourthNat.BPay_3193
  · exact WuPaper.ClassicalFourthNat.BPay_3194
  · exact WuPaper.ClassicalFourthNat.BPay_3195
  · exact WuPaper.ClassicalFourthNat.BPay_3196
  · exact WuPaper.ClassicalFourthNat.BPay_3197
  · exact WuPaper.ClassicalFourthNat.BPay_3198
  · exact WuPaper.ClassicalFourthNat.BPay_3199
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_049
