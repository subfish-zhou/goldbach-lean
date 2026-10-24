import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay052
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_052 (j : Fin 64) (hj : 64*52+j.val < 10540) :
    BPay (64*52+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3328
  · exact WuPaper.ClassicalFourthNat.BPay_3329
  · exact WuPaper.ClassicalFourthNat.BPay_3330
  · exact WuPaper.ClassicalFourthNat.BPay_3331
  · exact WuPaper.ClassicalFourthNat.BPay_3332
  · exact WuPaper.ClassicalFourthNat.BPay_3333
  · exact WuPaper.ClassicalFourthNat.BPay_3334
  · exact WuPaper.ClassicalFourthNat.BPay_3335
  · exact WuPaper.ClassicalFourthNat.BPay_3336
  · exact WuPaper.ClassicalFourthNat.BPay_3337
  · exact WuPaper.ClassicalFourthNat.BPay_3338
  · exact WuPaper.ClassicalFourthNat.BPay_3339
  · exact WuPaper.ClassicalFourthNat.BPay_3340
  · exact WuPaper.ClassicalFourthNat.BPay_3341
  · exact WuPaper.ClassicalFourthNat.BPay_3342
  · exact WuPaper.ClassicalFourthNat.BPay_3343
  · exact WuPaper.ClassicalFourthNat.BPay_3344
  · exact WuPaper.ClassicalFourthNat.BPay_3345
  · exact WuPaper.ClassicalFourthNat.BPay_3346
  · exact WuPaper.ClassicalFourthNat.BPay_3347
  · exact WuPaper.ClassicalFourthNat.BPay_3348
  · exact WuPaper.ClassicalFourthNat.BPay_3349
  · exact WuPaper.ClassicalFourthNat.BPay_3350
  · exact WuPaper.ClassicalFourthNat.BPay_3351
  · exact WuPaper.ClassicalFourthNat.BPay_3352
  · exact WuPaper.ClassicalFourthNat.BPay_3353
  · exact WuPaper.ClassicalFourthNat.BPay_3354
  · exact WuPaper.ClassicalFourthNat.BPay_3355
  · exact WuPaper.ClassicalFourthNat.BPay_3356
  · exact WuPaper.ClassicalFourthNat.BPay_3357
  · exact WuPaper.ClassicalFourthNat.BPay_3358
  · exact WuPaper.ClassicalFourthNat.BPay_3359
  · exact WuPaper.ClassicalFourthNat.BPay_3360
  · exact WuPaper.ClassicalFourthNat.BPay_3361
  · exact WuPaper.ClassicalFourthNat.BPay_3362
  · exact WuPaper.ClassicalFourthNat.BPay_3363
  · exact WuPaper.ClassicalFourthNat.BPay_3364
  · exact WuPaper.ClassicalFourthNat.BPay_3365
  · exact WuPaper.ClassicalFourthNat.BPay_3366
  · exact WuPaper.ClassicalFourthNat.BPay_3367
  · exact WuPaper.ClassicalFourthNat.BPay_3368
  · exact WuPaper.ClassicalFourthNat.BPay_3369
  · exact WuPaper.ClassicalFourthNat.BPay_3370
  · exact WuPaper.ClassicalFourthNat.BPay_3371
  · exact WuPaper.ClassicalFourthNat.BPay_3372
  · exact WuPaper.ClassicalFourthNat.BPay_3373
  · exact WuPaper.ClassicalFourthNat.BPay_3374
  · exact WuPaper.ClassicalFourthNat.BPay_3375
  · exact WuPaper.ClassicalFourthNat.BPay_3376
  · exact WuPaper.ClassicalFourthNat.BPay_3377
  · exact WuPaper.ClassicalFourthNat.BPay_3378
  · exact WuPaper.ClassicalFourthNat.BPay_3379
  · exact WuPaper.ClassicalFourthNat.BPay_3380
  · exact WuPaper.ClassicalFourthNat.BPay_3381
  · exact WuPaper.ClassicalFourthNat.BPay_3382
  · exact WuPaper.ClassicalFourthNat.BPay_3383
  · exact WuPaper.ClassicalFourthNat.BPay_3384
  · exact WuPaper.ClassicalFourthNat.BPay_3385
  · exact WuPaper.ClassicalFourthNat.BPay_3386
  · exact WuPaper.ClassicalFourthNat.BPay_3387
  · exact WuPaper.ClassicalFourthNat.BPay_3388
  · exact WuPaper.ClassicalFourthNat.BPay_3389
  · exact WuPaper.ClassicalFourthNat.BPay_3390
  · exact WuPaper.ClassicalFourthNat.BPay_3391
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_052
