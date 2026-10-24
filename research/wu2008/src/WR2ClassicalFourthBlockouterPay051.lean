import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay051
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_051 (j : Fin 64) (hj : 64*51+j.val < 10540) :
    OuterPay (64*51+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_3264
  · exact WuPaper.ClassicalFourthNat.outerPay_3265
  · exact WuPaper.ClassicalFourthNat.outerPay_3266
  · exact WuPaper.ClassicalFourthNat.outerPay_3267
  · exact WuPaper.ClassicalFourthNat.outerPay_3268
  · exact WuPaper.ClassicalFourthNat.outerPay_3269
  · exact WuPaper.ClassicalFourthNat.outerPay_3270
  · exact WuPaper.ClassicalFourthNat.outerPay_3271
  · exact WuPaper.ClassicalFourthNat.outerPay_3272
  · exact WuPaper.ClassicalFourthNat.outerPay_3273
  · exact WuPaper.ClassicalFourthNat.outerPay_3274
  · exact WuPaper.ClassicalFourthNat.outerPay_3275
  · exact WuPaper.ClassicalFourthNat.outerPay_3276
  · exact WuPaper.ClassicalFourthNat.outerPay_3277
  · exact WuPaper.ClassicalFourthNat.outerPay_3278
  · exact WuPaper.ClassicalFourthNat.outerPay_3279
  · exact WuPaper.ClassicalFourthNat.outerPay_3280
  · exact WuPaper.ClassicalFourthNat.outerPay_3281
  · exact WuPaper.ClassicalFourthNat.outerPay_3282
  · exact WuPaper.ClassicalFourthNat.outerPay_3283
  · exact WuPaper.ClassicalFourthNat.outerPay_3284
  · exact WuPaper.ClassicalFourthNat.outerPay_3285
  · exact WuPaper.ClassicalFourthNat.outerPay_3286
  · exact WuPaper.ClassicalFourthNat.outerPay_3287
  · exact WuPaper.ClassicalFourthNat.outerPay_3288
  · exact WuPaper.ClassicalFourthNat.outerPay_3289
  · exact WuPaper.ClassicalFourthNat.outerPay_3290
  · exact WuPaper.ClassicalFourthNat.outerPay_3291
  · exact WuPaper.ClassicalFourthNat.outerPay_3292
  · exact WuPaper.ClassicalFourthNat.outerPay_3293
  · exact WuPaper.ClassicalFourthNat.outerPay_3294
  · exact WuPaper.ClassicalFourthNat.outerPay_3295
  · exact WuPaper.ClassicalFourthNat.outerPay_3296
  · exact WuPaper.ClassicalFourthNat.outerPay_3297
  · exact WuPaper.ClassicalFourthNat.outerPay_3298
  · exact WuPaper.ClassicalFourthNat.outerPay_3299
  · exact WuPaper.ClassicalFourthNat.outerPay_3300
  · exact WuPaper.ClassicalFourthNat.outerPay_3301
  · exact WuPaper.ClassicalFourthNat.outerPay_3302
  · exact WuPaper.ClassicalFourthNat.outerPay_3303
  · exact WuPaper.ClassicalFourthNat.outerPay_3304
  · exact WuPaper.ClassicalFourthNat.outerPay_3305
  · exact WuPaper.ClassicalFourthNat.outerPay_3306
  · exact WuPaper.ClassicalFourthNat.outerPay_3307
  · exact WuPaper.ClassicalFourthNat.outerPay_3308
  · exact WuPaper.ClassicalFourthNat.outerPay_3309
  · exact WuPaper.ClassicalFourthNat.outerPay_3310
  · exact WuPaper.ClassicalFourthNat.outerPay_3311
  · exact WuPaper.ClassicalFourthNat.outerPay_3312
  · exact WuPaper.ClassicalFourthNat.outerPay_3313
  · exact WuPaper.ClassicalFourthNat.outerPay_3314
  · exact WuPaper.ClassicalFourthNat.outerPay_3315
  · exact WuPaper.ClassicalFourthNat.outerPay_3316
  · exact WuPaper.ClassicalFourthNat.outerPay_3317
  · exact WuPaper.ClassicalFourthNat.outerPay_3318
  · exact WuPaper.ClassicalFourthNat.outerPay_3319
  · exact WuPaper.ClassicalFourthNat.outerPay_3320
  · exact WuPaper.ClassicalFourthNat.outerPay_3321
  · exact WuPaper.ClassicalFourthNat.outerPay_3322
  · exact WuPaper.ClassicalFourthNat.outerPay_3323
  · exact WuPaper.ClassicalFourthNat.outerPay_3324
  · exact WuPaper.ClassicalFourthNat.outerPay_3325
  · exact WuPaper.ClassicalFourthNat.outerPay_3326
  · exact WuPaper.ClassicalFourthNat.outerPay_3327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_051
