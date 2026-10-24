import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay147
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_147 (j : Fin 64) (hj : 64*147+j.val < 10540) :
    BPay (64*147+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9408
  · exact WuPaper.ClassicalFourthNat.BPay_9409
  · exact WuPaper.ClassicalFourthNat.BPay_9410
  · exact WuPaper.ClassicalFourthNat.BPay_9411
  · exact WuPaper.ClassicalFourthNat.BPay_9412
  · exact WuPaper.ClassicalFourthNat.BPay_9413
  · exact WuPaper.ClassicalFourthNat.BPay_9414
  · exact WuPaper.ClassicalFourthNat.BPay_9415
  · exact WuPaper.ClassicalFourthNat.BPay_9416
  · exact WuPaper.ClassicalFourthNat.BPay_9417
  · exact WuPaper.ClassicalFourthNat.BPay_9418
  · exact WuPaper.ClassicalFourthNat.BPay_9419
  · exact WuPaper.ClassicalFourthNat.BPay_9420
  · exact WuPaper.ClassicalFourthNat.BPay_9421
  · exact WuPaper.ClassicalFourthNat.BPay_9422
  · exact WuPaper.ClassicalFourthNat.BPay_9423
  · exact WuPaper.ClassicalFourthNat.BPay_9424
  · exact WuPaper.ClassicalFourthNat.BPay_9425
  · exact WuPaper.ClassicalFourthNat.BPay_9426
  · exact WuPaper.ClassicalFourthNat.BPay_9427
  · exact WuPaper.ClassicalFourthNat.BPay_9428
  · exact WuPaper.ClassicalFourthNat.BPay_9429
  · exact WuPaper.ClassicalFourthNat.BPay_9430
  · exact WuPaper.ClassicalFourthNat.BPay_9431
  · exact WuPaper.ClassicalFourthNat.BPay_9432
  · exact WuPaper.ClassicalFourthNat.BPay_9433
  · exact WuPaper.ClassicalFourthNat.BPay_9434
  · exact WuPaper.ClassicalFourthNat.BPay_9435
  · exact WuPaper.ClassicalFourthNat.BPay_9436
  · exact WuPaper.ClassicalFourthNat.BPay_9437
  · exact WuPaper.ClassicalFourthNat.BPay_9438
  · exact WuPaper.ClassicalFourthNat.BPay_9439
  · exact WuPaper.ClassicalFourthNat.BPay_9440
  · exact WuPaper.ClassicalFourthNat.BPay_9441
  · exact WuPaper.ClassicalFourthNat.BPay_9442
  · exact WuPaper.ClassicalFourthNat.BPay_9443
  · exact WuPaper.ClassicalFourthNat.BPay_9444
  · exact WuPaper.ClassicalFourthNat.BPay_9445
  · exact WuPaper.ClassicalFourthNat.BPay_9446
  · exact WuPaper.ClassicalFourthNat.BPay_9447
  · exact WuPaper.ClassicalFourthNat.BPay_9448
  · exact WuPaper.ClassicalFourthNat.BPay_9449
  · exact WuPaper.ClassicalFourthNat.BPay_9450
  · exact WuPaper.ClassicalFourthNat.BPay_9451
  · exact WuPaper.ClassicalFourthNat.BPay_9452
  · exact WuPaper.ClassicalFourthNat.BPay_9453
  · exact WuPaper.ClassicalFourthNat.BPay_9454
  · exact WuPaper.ClassicalFourthNat.BPay_9455
  · exact WuPaper.ClassicalFourthNat.BPay_9456
  · exact WuPaper.ClassicalFourthNat.BPay_9457
  · exact WuPaper.ClassicalFourthNat.BPay_9458
  · exact WuPaper.ClassicalFourthNat.BPay_9459
  · exact WuPaper.ClassicalFourthNat.BPay_9460
  · exact WuPaper.ClassicalFourthNat.BPay_9461
  · exact WuPaper.ClassicalFourthNat.BPay_9462
  · exact WuPaper.ClassicalFourthNat.BPay_9463
  · exact WuPaper.ClassicalFourthNat.BPay_9464
  · exact WuPaper.ClassicalFourthNat.BPay_9465
  · exact WuPaper.ClassicalFourthNat.BPay_9466
  · exact WuPaper.ClassicalFourthNat.BPay_9467
  · exact WuPaper.ClassicalFourthNat.BPay_9468
  · exact WuPaper.ClassicalFourthNat.BPay_9469
  · exact WuPaper.ClassicalFourthNat.BPay_9470
  · exact WuPaper.ClassicalFourthNat.BPay_9471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_147
