import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay038
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_038 (j : Fin 64) (hj : 64*38+j.val < 10540) :
    BPay (64*38+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2432
  · exact WuPaper.ClassicalFourthNat.BPay_2433
  · exact WuPaper.ClassicalFourthNat.BPay_2434
  · exact WuPaper.ClassicalFourthNat.BPay_2435
  · exact WuPaper.ClassicalFourthNat.BPay_2436
  · exact WuPaper.ClassicalFourthNat.BPay_2437
  · exact WuPaper.ClassicalFourthNat.BPay_2438
  · exact WuPaper.ClassicalFourthNat.BPay_2439
  · exact WuPaper.ClassicalFourthNat.BPay_2440
  · exact WuPaper.ClassicalFourthNat.BPay_2441
  · exact WuPaper.ClassicalFourthNat.BPay_2442
  · exact WuPaper.ClassicalFourthNat.BPay_2443
  · exact WuPaper.ClassicalFourthNat.BPay_2444
  · exact WuPaper.ClassicalFourthNat.BPay_2445
  · exact WuPaper.ClassicalFourthNat.BPay_2446
  · exact WuPaper.ClassicalFourthNat.BPay_2447
  · exact WuPaper.ClassicalFourthNat.BPay_2448
  · exact WuPaper.ClassicalFourthNat.BPay_2449
  · exact WuPaper.ClassicalFourthNat.BPay_2450
  · exact WuPaper.ClassicalFourthNat.BPay_2451
  · exact WuPaper.ClassicalFourthNat.BPay_2452
  · exact WuPaper.ClassicalFourthNat.BPay_2453
  · exact WuPaper.ClassicalFourthNat.BPay_2454
  · exact WuPaper.ClassicalFourthNat.BPay_2455
  · exact WuPaper.ClassicalFourthNat.BPay_2456
  · exact WuPaper.ClassicalFourthNat.BPay_2457
  · exact WuPaper.ClassicalFourthNat.BPay_2458
  · exact WuPaper.ClassicalFourthNat.BPay_2459
  · exact WuPaper.ClassicalFourthNat.BPay_2460
  · exact WuPaper.ClassicalFourthNat.BPay_2461
  · exact WuPaper.ClassicalFourthNat.BPay_2462
  · exact WuPaper.ClassicalFourthNat.BPay_2463
  · exact WuPaper.ClassicalFourthNat.BPay_2464
  · exact WuPaper.ClassicalFourthNat.BPay_2465
  · exact WuPaper.ClassicalFourthNat.BPay_2466
  · exact WuPaper.ClassicalFourthNat.BPay_2467
  · exact WuPaper.ClassicalFourthNat.BPay_2468
  · exact WuPaper.ClassicalFourthNat.BPay_2469
  · exact WuPaper.ClassicalFourthNat.BPay_2470
  · exact WuPaper.ClassicalFourthNat.BPay_2471
  · exact WuPaper.ClassicalFourthNat.BPay_2472
  · exact WuPaper.ClassicalFourthNat.BPay_2473
  · exact WuPaper.ClassicalFourthNat.BPay_2474
  · exact WuPaper.ClassicalFourthNat.BPay_2475
  · exact WuPaper.ClassicalFourthNat.BPay_2476
  · exact WuPaper.ClassicalFourthNat.BPay_2477
  · exact WuPaper.ClassicalFourthNat.BPay_2478
  · exact WuPaper.ClassicalFourthNat.BPay_2479
  · exact WuPaper.ClassicalFourthNat.BPay_2480
  · exact WuPaper.ClassicalFourthNat.BPay_2481
  · exact WuPaper.ClassicalFourthNat.BPay_2482
  · exact WuPaper.ClassicalFourthNat.BPay_2483
  · exact WuPaper.ClassicalFourthNat.BPay_2484
  · exact WuPaper.ClassicalFourthNat.BPay_2485
  · exact WuPaper.ClassicalFourthNat.BPay_2486
  · exact WuPaper.ClassicalFourthNat.BPay_2487
  · exact WuPaper.ClassicalFourthNat.BPay_2488
  · exact WuPaper.ClassicalFourthNat.BPay_2489
  · exact WuPaper.ClassicalFourthNat.BPay_2490
  · exact WuPaper.ClassicalFourthNat.BPay_2491
  · exact WuPaper.ClassicalFourthNat.BPay_2492
  · exact WuPaper.ClassicalFourthNat.BPay_2493
  · exact WuPaper.ClassicalFourthNat.BPay_2494
  · exact WuPaper.ClassicalFourthNat.BPay_2495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_038
