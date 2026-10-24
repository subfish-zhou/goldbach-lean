import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay115
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_115 (j : Fin 64) (hj : 64*115+j.val < 10540) :
    BPay (64*115+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7360
  · exact WuPaper.ClassicalFourthNat.BPay_7361
  · exact WuPaper.ClassicalFourthNat.BPay_7362
  · exact WuPaper.ClassicalFourthNat.BPay_7363
  · exact WuPaper.ClassicalFourthNat.BPay_7364
  · exact WuPaper.ClassicalFourthNat.BPay_7365
  · exact WuPaper.ClassicalFourthNat.BPay_7366
  · exact WuPaper.ClassicalFourthNat.BPay_7367
  · exact WuPaper.ClassicalFourthNat.BPay_7368
  · exact WuPaper.ClassicalFourthNat.BPay_7369
  · exact WuPaper.ClassicalFourthNat.BPay_7370
  · exact WuPaper.ClassicalFourthNat.BPay_7371
  · exact WuPaper.ClassicalFourthNat.BPay_7372
  · exact WuPaper.ClassicalFourthNat.BPay_7373
  · exact WuPaper.ClassicalFourthNat.BPay_7374
  · exact WuPaper.ClassicalFourthNat.BPay_7375
  · exact WuPaper.ClassicalFourthNat.BPay_7376
  · exact WuPaper.ClassicalFourthNat.BPay_7377
  · exact WuPaper.ClassicalFourthNat.BPay_7378
  · exact WuPaper.ClassicalFourthNat.BPay_7379
  · exact WuPaper.ClassicalFourthNat.BPay_7380
  · exact WuPaper.ClassicalFourthNat.BPay_7381
  · exact WuPaper.ClassicalFourthNat.BPay_7382
  · exact WuPaper.ClassicalFourthNat.BPay_7383
  · exact WuPaper.ClassicalFourthNat.BPay_7384
  · exact WuPaper.ClassicalFourthNat.BPay_7385
  · exact WuPaper.ClassicalFourthNat.BPay_7386
  · exact WuPaper.ClassicalFourthNat.BPay_7387
  · exact WuPaper.ClassicalFourthNat.BPay_7388
  · exact WuPaper.ClassicalFourthNat.BPay_7389
  · exact WuPaper.ClassicalFourthNat.BPay_7390
  · exact WuPaper.ClassicalFourthNat.BPay_7391
  · exact WuPaper.ClassicalFourthNat.BPay_7392
  · exact WuPaper.ClassicalFourthNat.BPay_7393
  · exact WuPaper.ClassicalFourthNat.BPay_7394
  · exact WuPaper.ClassicalFourthNat.BPay_7395
  · exact WuPaper.ClassicalFourthNat.BPay_7396
  · exact WuPaper.ClassicalFourthNat.BPay_7397
  · exact WuPaper.ClassicalFourthNat.BPay_7398
  · exact WuPaper.ClassicalFourthNat.BPay_7399
  · exact WuPaper.ClassicalFourthNat.BPay_7400
  · exact WuPaper.ClassicalFourthNat.BPay_7401
  · exact WuPaper.ClassicalFourthNat.BPay_7402
  · exact WuPaper.ClassicalFourthNat.BPay_7403
  · exact WuPaper.ClassicalFourthNat.BPay_7404
  · exact WuPaper.ClassicalFourthNat.BPay_7405
  · exact WuPaper.ClassicalFourthNat.BPay_7406
  · exact WuPaper.ClassicalFourthNat.BPay_7407
  · exact WuPaper.ClassicalFourthNat.BPay_7408
  · exact WuPaper.ClassicalFourthNat.BPay_7409
  · exact WuPaper.ClassicalFourthNat.BPay_7410
  · exact WuPaper.ClassicalFourthNat.BPay_7411
  · exact WuPaper.ClassicalFourthNat.BPay_7412
  · exact WuPaper.ClassicalFourthNat.BPay_7413
  · exact WuPaper.ClassicalFourthNat.BPay_7414
  · exact WuPaper.ClassicalFourthNat.BPay_7415
  · exact WuPaper.ClassicalFourthNat.BPay_7416
  · exact WuPaper.ClassicalFourthNat.BPay_7417
  · exact WuPaper.ClassicalFourthNat.BPay_7418
  · exact WuPaper.ClassicalFourthNat.BPay_7419
  · exact WuPaper.ClassicalFourthNat.BPay_7420
  · exact WuPaper.ClassicalFourthNat.BPay_7421
  · exact WuPaper.ClassicalFourthNat.BPay_7422
  · exact WuPaper.ClassicalFourthNat.BPay_7423
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_115
