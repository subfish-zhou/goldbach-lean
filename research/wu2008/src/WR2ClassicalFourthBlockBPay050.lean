import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay050
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_050 (j : Fin 64) (hj : 64*50+j.val < 10540) :
    BPay (64*50+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3200
  · exact WuPaper.ClassicalFourthNat.BPay_3201
  · exact WuPaper.ClassicalFourthNat.BPay_3202
  · exact WuPaper.ClassicalFourthNat.BPay_3203
  · exact WuPaper.ClassicalFourthNat.BPay_3204
  · exact WuPaper.ClassicalFourthNat.BPay_3205
  · exact WuPaper.ClassicalFourthNat.BPay_3206
  · exact WuPaper.ClassicalFourthNat.BPay_3207
  · exact WuPaper.ClassicalFourthNat.BPay_3208
  · exact WuPaper.ClassicalFourthNat.BPay_3209
  · exact WuPaper.ClassicalFourthNat.BPay_3210
  · exact WuPaper.ClassicalFourthNat.BPay_3211
  · exact WuPaper.ClassicalFourthNat.BPay_3212
  · exact WuPaper.ClassicalFourthNat.BPay_3213
  · exact WuPaper.ClassicalFourthNat.BPay_3214
  · exact WuPaper.ClassicalFourthNat.BPay_3215
  · exact WuPaper.ClassicalFourthNat.BPay_3216
  · exact WuPaper.ClassicalFourthNat.BPay_3217
  · exact WuPaper.ClassicalFourthNat.BPay_3218
  · exact WuPaper.ClassicalFourthNat.BPay_3219
  · exact WuPaper.ClassicalFourthNat.BPay_3220
  · exact WuPaper.ClassicalFourthNat.BPay_3221
  · exact WuPaper.ClassicalFourthNat.BPay_3222
  · exact WuPaper.ClassicalFourthNat.BPay_3223
  · exact WuPaper.ClassicalFourthNat.BPay_3224
  · exact WuPaper.ClassicalFourthNat.BPay_3225
  · exact WuPaper.ClassicalFourthNat.BPay_3226
  · exact WuPaper.ClassicalFourthNat.BPay_3227
  · exact WuPaper.ClassicalFourthNat.BPay_3228
  · exact WuPaper.ClassicalFourthNat.BPay_3229
  · exact WuPaper.ClassicalFourthNat.BPay_3230
  · exact WuPaper.ClassicalFourthNat.BPay_3231
  · exact WuPaper.ClassicalFourthNat.BPay_3232
  · exact WuPaper.ClassicalFourthNat.BPay_3233
  · exact WuPaper.ClassicalFourthNat.BPay_3234
  · exact WuPaper.ClassicalFourthNat.BPay_3235
  · exact WuPaper.ClassicalFourthNat.BPay_3236
  · exact WuPaper.ClassicalFourthNat.BPay_3237
  · exact WuPaper.ClassicalFourthNat.BPay_3238
  · exact WuPaper.ClassicalFourthNat.BPay_3239
  · exact WuPaper.ClassicalFourthNat.BPay_3240
  · exact WuPaper.ClassicalFourthNat.BPay_3241
  · exact WuPaper.ClassicalFourthNat.BPay_3242
  · exact WuPaper.ClassicalFourthNat.BPay_3243
  · exact WuPaper.ClassicalFourthNat.BPay_3244
  · exact WuPaper.ClassicalFourthNat.BPay_3245
  · exact WuPaper.ClassicalFourthNat.BPay_3246
  · exact WuPaper.ClassicalFourthNat.BPay_3247
  · exact WuPaper.ClassicalFourthNat.BPay_3248
  · exact WuPaper.ClassicalFourthNat.BPay_3249
  · exact WuPaper.ClassicalFourthNat.BPay_3250
  · exact WuPaper.ClassicalFourthNat.BPay_3251
  · exact WuPaper.ClassicalFourthNat.BPay_3252
  · exact WuPaper.ClassicalFourthNat.BPay_3253
  · exact WuPaper.ClassicalFourthNat.BPay_3254
  · exact WuPaper.ClassicalFourthNat.BPay_3255
  · exact WuPaper.ClassicalFourthNat.BPay_3256
  · exact WuPaper.ClassicalFourthNat.BPay_3257
  · exact WuPaper.ClassicalFourthNat.BPay_3258
  · exact WuPaper.ClassicalFourthNat.BPay_3259
  · exact WuPaper.ClassicalFourthNat.BPay_3260
  · exact WuPaper.ClassicalFourthNat.BPay_3261
  · exact WuPaper.ClassicalFourthNat.BPay_3262
  · exact WuPaper.ClassicalFourthNat.BPay_3263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_050
