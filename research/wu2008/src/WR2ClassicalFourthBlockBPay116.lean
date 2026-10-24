import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay116
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_116 (j : Fin 64) (hj : 64*116+j.val < 10540) :
    BPay (64*116+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7424
  · exact WuPaper.ClassicalFourthNat.BPay_7425
  · exact WuPaper.ClassicalFourthNat.BPay_7426
  · exact WuPaper.ClassicalFourthNat.BPay_7427
  · exact WuPaper.ClassicalFourthNat.BPay_7428
  · exact WuPaper.ClassicalFourthNat.BPay_7429
  · exact WuPaper.ClassicalFourthNat.BPay_7430
  · exact WuPaper.ClassicalFourthNat.BPay_7431
  · exact WuPaper.ClassicalFourthNat.BPay_7432
  · exact WuPaper.ClassicalFourthNat.BPay_7433
  · exact WuPaper.ClassicalFourthNat.BPay_7434
  · exact WuPaper.ClassicalFourthNat.BPay_7435
  · exact WuPaper.ClassicalFourthNat.BPay_7436
  · exact WuPaper.ClassicalFourthNat.BPay_7437
  · exact WuPaper.ClassicalFourthNat.BPay_7438
  · exact WuPaper.ClassicalFourthNat.BPay_7439
  · exact WuPaper.ClassicalFourthNat.BPay_7440
  · exact WuPaper.ClassicalFourthNat.BPay_7441
  · exact WuPaper.ClassicalFourthNat.BPay_7442
  · exact WuPaper.ClassicalFourthNat.BPay_7443
  · exact WuPaper.ClassicalFourthNat.BPay_7444
  · exact WuPaper.ClassicalFourthNat.BPay_7445
  · exact WuPaper.ClassicalFourthNat.BPay_7446
  · exact WuPaper.ClassicalFourthNat.BPay_7447
  · exact WuPaper.ClassicalFourthNat.BPay_7448
  · exact WuPaper.ClassicalFourthNat.BPay_7449
  · exact WuPaper.ClassicalFourthNat.BPay_7450
  · exact WuPaper.ClassicalFourthNat.BPay_7451
  · exact WuPaper.ClassicalFourthNat.BPay_7452
  · exact WuPaper.ClassicalFourthNat.BPay_7453
  · exact WuPaper.ClassicalFourthNat.BPay_7454
  · exact WuPaper.ClassicalFourthNat.BPay_7455
  · exact WuPaper.ClassicalFourthNat.BPay_7456
  · exact WuPaper.ClassicalFourthNat.BPay_7457
  · exact WuPaper.ClassicalFourthNat.BPay_7458
  · exact WuPaper.ClassicalFourthNat.BPay_7459
  · exact WuPaper.ClassicalFourthNat.BPay_7460
  · exact WuPaper.ClassicalFourthNat.BPay_7461
  · exact WuPaper.ClassicalFourthNat.BPay_7462
  · exact WuPaper.ClassicalFourthNat.BPay_7463
  · exact WuPaper.ClassicalFourthNat.BPay_7464
  · exact WuPaper.ClassicalFourthNat.BPay_7465
  · exact WuPaper.ClassicalFourthNat.BPay_7466
  · exact WuPaper.ClassicalFourthNat.BPay_7467
  · exact WuPaper.ClassicalFourthNat.BPay_7468
  · exact WuPaper.ClassicalFourthNat.BPay_7469
  · exact WuPaper.ClassicalFourthNat.BPay_7470
  · exact WuPaper.ClassicalFourthNat.BPay_7471
  · exact WuPaper.ClassicalFourthNat.BPay_7472
  · exact WuPaper.ClassicalFourthNat.BPay_7473
  · exact WuPaper.ClassicalFourthNat.BPay_7474
  · exact WuPaper.ClassicalFourthNat.BPay_7475
  · exact WuPaper.ClassicalFourthNat.BPay_7476
  · exact WuPaper.ClassicalFourthNat.BPay_7477
  · exact WuPaper.ClassicalFourthNat.BPay_7478
  · exact WuPaper.ClassicalFourthNat.BPay_7479
  · exact WuPaper.ClassicalFourthNat.BPay_7480
  · exact WuPaper.ClassicalFourthNat.BPay_7481
  · exact WuPaper.ClassicalFourthNat.BPay_7482
  · exact WuPaper.ClassicalFourthNat.BPay_7483
  · exact WuPaper.ClassicalFourthNat.BPay_7484
  · exact WuPaper.ClassicalFourthNat.BPay_7485
  · exact WuPaper.ClassicalFourthNat.BPay_7486
  · exact WuPaper.ClassicalFourthNat.BPay_7487
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_116
