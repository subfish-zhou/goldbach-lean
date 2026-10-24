import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay051
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_051 (j : Fin 64) (hj : 64*51+j.val < 10540) :
    BPay (64*51+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3264
  · exact WuPaper.ClassicalFourthNat.BPay_3265
  · exact WuPaper.ClassicalFourthNat.BPay_3266
  · exact WuPaper.ClassicalFourthNat.BPay_3267
  · exact WuPaper.ClassicalFourthNat.BPay_3268
  · exact WuPaper.ClassicalFourthNat.BPay_3269
  · exact WuPaper.ClassicalFourthNat.BPay_3270
  · exact WuPaper.ClassicalFourthNat.BPay_3271
  · exact WuPaper.ClassicalFourthNat.BPay_3272
  · exact WuPaper.ClassicalFourthNat.BPay_3273
  · exact WuPaper.ClassicalFourthNat.BPay_3274
  · exact WuPaper.ClassicalFourthNat.BPay_3275
  · exact WuPaper.ClassicalFourthNat.BPay_3276
  · exact WuPaper.ClassicalFourthNat.BPay_3277
  · exact WuPaper.ClassicalFourthNat.BPay_3278
  · exact WuPaper.ClassicalFourthNat.BPay_3279
  · exact WuPaper.ClassicalFourthNat.BPay_3280
  · exact WuPaper.ClassicalFourthNat.BPay_3281
  · exact WuPaper.ClassicalFourthNat.BPay_3282
  · exact WuPaper.ClassicalFourthNat.BPay_3283
  · exact WuPaper.ClassicalFourthNat.BPay_3284
  · exact WuPaper.ClassicalFourthNat.BPay_3285
  · exact WuPaper.ClassicalFourthNat.BPay_3286
  · exact WuPaper.ClassicalFourthNat.BPay_3287
  · exact WuPaper.ClassicalFourthNat.BPay_3288
  · exact WuPaper.ClassicalFourthNat.BPay_3289
  · exact WuPaper.ClassicalFourthNat.BPay_3290
  · exact WuPaper.ClassicalFourthNat.BPay_3291
  · exact WuPaper.ClassicalFourthNat.BPay_3292
  · exact WuPaper.ClassicalFourthNat.BPay_3293
  · exact WuPaper.ClassicalFourthNat.BPay_3294
  · exact WuPaper.ClassicalFourthNat.BPay_3295
  · exact WuPaper.ClassicalFourthNat.BPay_3296
  · exact WuPaper.ClassicalFourthNat.BPay_3297
  · exact WuPaper.ClassicalFourthNat.BPay_3298
  · exact WuPaper.ClassicalFourthNat.BPay_3299
  · exact WuPaper.ClassicalFourthNat.BPay_3300
  · exact WuPaper.ClassicalFourthNat.BPay_3301
  · exact WuPaper.ClassicalFourthNat.BPay_3302
  · exact WuPaper.ClassicalFourthNat.BPay_3303
  · exact WuPaper.ClassicalFourthNat.BPay_3304
  · exact WuPaper.ClassicalFourthNat.BPay_3305
  · exact WuPaper.ClassicalFourthNat.BPay_3306
  · exact WuPaper.ClassicalFourthNat.BPay_3307
  · exact WuPaper.ClassicalFourthNat.BPay_3308
  · exact WuPaper.ClassicalFourthNat.BPay_3309
  · exact WuPaper.ClassicalFourthNat.BPay_3310
  · exact WuPaper.ClassicalFourthNat.BPay_3311
  · exact WuPaper.ClassicalFourthNat.BPay_3312
  · exact WuPaper.ClassicalFourthNat.BPay_3313
  · exact WuPaper.ClassicalFourthNat.BPay_3314
  · exact WuPaper.ClassicalFourthNat.BPay_3315
  · exact WuPaper.ClassicalFourthNat.BPay_3316
  · exact WuPaper.ClassicalFourthNat.BPay_3317
  · exact WuPaper.ClassicalFourthNat.BPay_3318
  · exact WuPaper.ClassicalFourthNat.BPay_3319
  · exact WuPaper.ClassicalFourthNat.BPay_3320
  · exact WuPaper.ClassicalFourthNat.BPay_3321
  · exact WuPaper.ClassicalFourthNat.BPay_3322
  · exact WuPaper.ClassicalFourthNat.BPay_3323
  · exact WuPaper.ClassicalFourthNat.BPay_3324
  · exact WuPaper.ClassicalFourthNat.BPay_3325
  · exact WuPaper.ClassicalFourthNat.BPay_3326
  · exact WuPaper.ClassicalFourthNat.BPay_3327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_051
