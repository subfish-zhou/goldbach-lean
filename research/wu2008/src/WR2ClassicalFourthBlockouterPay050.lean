import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay050
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_050 (j : Fin 64) (hj : 64*50+j.val < 10540) :
    OuterPay (64*50+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_3200
  · exact WuPaper.ClassicalFourthNat.outerPay_3201
  · exact WuPaper.ClassicalFourthNat.outerPay_3202
  · exact WuPaper.ClassicalFourthNat.outerPay_3203
  · exact WuPaper.ClassicalFourthNat.outerPay_3204
  · exact WuPaper.ClassicalFourthNat.outerPay_3205
  · exact WuPaper.ClassicalFourthNat.outerPay_3206
  · exact WuPaper.ClassicalFourthNat.outerPay_3207
  · exact WuPaper.ClassicalFourthNat.outerPay_3208
  · exact WuPaper.ClassicalFourthNat.outerPay_3209
  · exact WuPaper.ClassicalFourthNat.outerPay_3210
  · exact WuPaper.ClassicalFourthNat.outerPay_3211
  · exact WuPaper.ClassicalFourthNat.outerPay_3212
  · exact WuPaper.ClassicalFourthNat.outerPay_3213
  · exact WuPaper.ClassicalFourthNat.outerPay_3214
  · exact WuPaper.ClassicalFourthNat.outerPay_3215
  · exact WuPaper.ClassicalFourthNat.outerPay_3216
  · exact WuPaper.ClassicalFourthNat.outerPay_3217
  · exact WuPaper.ClassicalFourthNat.outerPay_3218
  · exact WuPaper.ClassicalFourthNat.outerPay_3219
  · exact WuPaper.ClassicalFourthNat.outerPay_3220
  · exact WuPaper.ClassicalFourthNat.outerPay_3221
  · exact WuPaper.ClassicalFourthNat.outerPay_3222
  · exact WuPaper.ClassicalFourthNat.outerPay_3223
  · exact WuPaper.ClassicalFourthNat.outerPay_3224
  · exact WuPaper.ClassicalFourthNat.outerPay_3225
  · exact WuPaper.ClassicalFourthNat.outerPay_3226
  · exact WuPaper.ClassicalFourthNat.outerPay_3227
  · exact WuPaper.ClassicalFourthNat.outerPay_3228
  · exact WuPaper.ClassicalFourthNat.outerPay_3229
  · exact WuPaper.ClassicalFourthNat.outerPay_3230
  · exact WuPaper.ClassicalFourthNat.outerPay_3231
  · exact WuPaper.ClassicalFourthNat.outerPay_3232
  · exact WuPaper.ClassicalFourthNat.outerPay_3233
  · exact WuPaper.ClassicalFourthNat.outerPay_3234
  · exact WuPaper.ClassicalFourthNat.outerPay_3235
  · exact WuPaper.ClassicalFourthNat.outerPay_3236
  · exact WuPaper.ClassicalFourthNat.outerPay_3237
  · exact WuPaper.ClassicalFourthNat.outerPay_3238
  · exact WuPaper.ClassicalFourthNat.outerPay_3239
  · exact WuPaper.ClassicalFourthNat.outerPay_3240
  · exact WuPaper.ClassicalFourthNat.outerPay_3241
  · exact WuPaper.ClassicalFourthNat.outerPay_3242
  · exact WuPaper.ClassicalFourthNat.outerPay_3243
  · exact WuPaper.ClassicalFourthNat.outerPay_3244
  · exact WuPaper.ClassicalFourthNat.outerPay_3245
  · exact WuPaper.ClassicalFourthNat.outerPay_3246
  · exact WuPaper.ClassicalFourthNat.outerPay_3247
  · exact WuPaper.ClassicalFourthNat.outerPay_3248
  · exact WuPaper.ClassicalFourthNat.outerPay_3249
  · exact WuPaper.ClassicalFourthNat.outerPay_3250
  · exact WuPaper.ClassicalFourthNat.outerPay_3251
  · exact WuPaper.ClassicalFourthNat.outerPay_3252
  · exact WuPaper.ClassicalFourthNat.outerPay_3253
  · exact WuPaper.ClassicalFourthNat.outerPay_3254
  · exact WuPaper.ClassicalFourthNat.outerPay_3255
  · exact WuPaper.ClassicalFourthNat.outerPay_3256
  · exact WuPaper.ClassicalFourthNat.outerPay_3257
  · exact WuPaper.ClassicalFourthNat.outerPay_3258
  · exact WuPaper.ClassicalFourthNat.outerPay_3259
  · exact WuPaper.ClassicalFourthNat.outerPay_3260
  · exact WuPaper.ClassicalFourthNat.outerPay_3261
  · exact WuPaper.ClassicalFourthNat.outerPay_3262
  · exact WuPaper.ClassicalFourthNat.outerPay_3263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_050
