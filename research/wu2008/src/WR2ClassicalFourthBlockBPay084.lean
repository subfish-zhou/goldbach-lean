import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay084
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_084 (j : Fin 64) (hj : 64*84+j.val < 10540) :
    BPay (64*84+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5376
  · exact WuPaper.ClassicalFourthNat.BPay_5377
  · exact WuPaper.ClassicalFourthNat.BPay_5378
  · exact WuPaper.ClassicalFourthNat.BPay_5379
  · exact WuPaper.ClassicalFourthNat.BPay_5380
  · exact WuPaper.ClassicalFourthNat.BPay_5381
  · exact WuPaper.ClassicalFourthNat.BPay_5382
  · exact WuPaper.ClassicalFourthNat.BPay_5383
  · exact WuPaper.ClassicalFourthNat.BPay_5384
  · exact WuPaper.ClassicalFourthNat.BPay_5385
  · exact WuPaper.ClassicalFourthNat.BPay_5386
  · exact WuPaper.ClassicalFourthNat.BPay_5387
  · exact WuPaper.ClassicalFourthNat.BPay_5388
  · exact WuPaper.ClassicalFourthNat.BPay_5389
  · exact WuPaper.ClassicalFourthNat.BPay_5390
  · exact WuPaper.ClassicalFourthNat.BPay_5391
  · exact WuPaper.ClassicalFourthNat.BPay_5392
  · exact WuPaper.ClassicalFourthNat.BPay_5393
  · exact WuPaper.ClassicalFourthNat.BPay_5394
  · exact WuPaper.ClassicalFourthNat.BPay_5395
  · exact WuPaper.ClassicalFourthNat.BPay_5396
  · exact WuPaper.ClassicalFourthNat.BPay_5397
  · exact WuPaper.ClassicalFourthNat.BPay_5398
  · exact WuPaper.ClassicalFourthNat.BPay_5399
  · exact WuPaper.ClassicalFourthNat.BPay_5400
  · exact WuPaper.ClassicalFourthNat.BPay_5401
  · exact WuPaper.ClassicalFourthNat.BPay_5402
  · exact WuPaper.ClassicalFourthNat.BPay_5403
  · exact WuPaper.ClassicalFourthNat.BPay_5404
  · exact WuPaper.ClassicalFourthNat.BPay_5405
  · exact WuPaper.ClassicalFourthNat.BPay_5406
  · exact WuPaper.ClassicalFourthNat.BPay_5407
  · exact WuPaper.ClassicalFourthNat.BPay_5408
  · exact WuPaper.ClassicalFourthNat.BPay_5409
  · exact WuPaper.ClassicalFourthNat.BPay_5410
  · exact WuPaper.ClassicalFourthNat.BPay_5411
  · exact WuPaper.ClassicalFourthNat.BPay_5412
  · exact WuPaper.ClassicalFourthNat.BPay_5413
  · exact WuPaper.ClassicalFourthNat.BPay_5414
  · exact WuPaper.ClassicalFourthNat.BPay_5415
  · exact WuPaper.ClassicalFourthNat.BPay_5416
  · exact WuPaper.ClassicalFourthNat.BPay_5417
  · exact WuPaper.ClassicalFourthNat.BPay_5418
  · exact WuPaper.ClassicalFourthNat.BPay_5419
  · exact WuPaper.ClassicalFourthNat.BPay_5420
  · exact WuPaper.ClassicalFourthNat.BPay_5421
  · exact WuPaper.ClassicalFourthNat.BPay_5422
  · exact WuPaper.ClassicalFourthNat.BPay_5423
  · exact WuPaper.ClassicalFourthNat.BPay_5424
  · exact WuPaper.ClassicalFourthNat.BPay_5425
  · exact WuPaper.ClassicalFourthNat.BPay_5426
  · exact WuPaper.ClassicalFourthNat.BPay_5427
  · exact WuPaper.ClassicalFourthNat.BPay_5428
  · exact WuPaper.ClassicalFourthNat.BPay_5429
  · exact WuPaper.ClassicalFourthNat.BPay_5430
  · exact WuPaper.ClassicalFourthNat.BPay_5431
  · exact WuPaper.ClassicalFourthNat.BPay_5432
  · exact WuPaper.ClassicalFourthNat.BPay_5433
  · exact WuPaper.ClassicalFourthNat.BPay_5434
  · exact WuPaper.ClassicalFourthNat.BPay_5435
  · exact WuPaper.ClassicalFourthNat.BPay_5436
  · exact WuPaper.ClassicalFourthNat.BPay_5437
  · exact WuPaper.ClassicalFourthNat.BPay_5438
  · exact WuPaper.ClassicalFourthNat.BPay_5439
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_084
