import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay038
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_038 (j : Fin 64) (hj : 64*38+j.val < 2540) :
    DPay (64*38+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_2432
  · exact WuPaper.ClassicalFourthNat.DPay_2433
  · exact WuPaper.ClassicalFourthNat.DPay_2434
  · exact WuPaper.ClassicalFourthNat.DPay_2435
  · exact WuPaper.ClassicalFourthNat.DPay_2436
  · exact WuPaper.ClassicalFourthNat.DPay_2437
  · exact WuPaper.ClassicalFourthNat.DPay_2438
  · exact WuPaper.ClassicalFourthNat.DPay_2439
  · exact WuPaper.ClassicalFourthNat.DPay_2440
  · exact WuPaper.ClassicalFourthNat.DPay_2441
  · exact WuPaper.ClassicalFourthNat.DPay_2442
  · exact WuPaper.ClassicalFourthNat.DPay_2443
  · exact WuPaper.ClassicalFourthNat.DPay_2444
  · exact WuPaper.ClassicalFourthNat.DPay_2445
  · exact WuPaper.ClassicalFourthNat.DPay_2446
  · exact WuPaper.ClassicalFourthNat.DPay_2447
  · exact WuPaper.ClassicalFourthNat.DPay_2448
  · exact WuPaper.ClassicalFourthNat.DPay_2449
  · exact WuPaper.ClassicalFourthNat.DPay_2450
  · exact WuPaper.ClassicalFourthNat.DPay_2451
  · exact WuPaper.ClassicalFourthNat.DPay_2452
  · exact WuPaper.ClassicalFourthNat.DPay_2453
  · exact WuPaper.ClassicalFourthNat.DPay_2454
  · exact WuPaper.ClassicalFourthNat.DPay_2455
  · exact WuPaper.ClassicalFourthNat.DPay_2456
  · exact WuPaper.ClassicalFourthNat.DPay_2457
  · exact WuPaper.ClassicalFourthNat.DPay_2458
  · exact WuPaper.ClassicalFourthNat.DPay_2459
  · exact WuPaper.ClassicalFourthNat.DPay_2460
  · exact WuPaper.ClassicalFourthNat.DPay_2461
  · exact WuPaper.ClassicalFourthNat.DPay_2462
  · exact WuPaper.ClassicalFourthNat.DPay_2463
  · exact WuPaper.ClassicalFourthNat.DPay_2464
  · exact WuPaper.ClassicalFourthNat.DPay_2465
  · exact WuPaper.ClassicalFourthNat.DPay_2466
  · exact WuPaper.ClassicalFourthNat.DPay_2467
  · exact WuPaper.ClassicalFourthNat.DPay_2468
  · exact WuPaper.ClassicalFourthNat.DPay_2469
  · exact WuPaper.ClassicalFourthNat.DPay_2470
  · exact WuPaper.ClassicalFourthNat.DPay_2471
  · exact WuPaper.ClassicalFourthNat.DPay_2472
  · exact WuPaper.ClassicalFourthNat.DPay_2473
  · exact WuPaper.ClassicalFourthNat.DPay_2474
  · exact WuPaper.ClassicalFourthNat.DPay_2475
  · exact WuPaper.ClassicalFourthNat.DPay_2476
  · exact WuPaper.ClassicalFourthNat.DPay_2477
  · exact WuPaper.ClassicalFourthNat.DPay_2478
  · exact WuPaper.ClassicalFourthNat.DPay_2479
  · exact WuPaper.ClassicalFourthNat.DPay_2480
  · exact WuPaper.ClassicalFourthNat.DPay_2481
  · exact WuPaper.ClassicalFourthNat.DPay_2482
  · exact WuPaper.ClassicalFourthNat.DPay_2483
  · exact WuPaper.ClassicalFourthNat.DPay_2484
  · exact WuPaper.ClassicalFourthNat.DPay_2485
  · exact WuPaper.ClassicalFourthNat.DPay_2486
  · exact WuPaper.ClassicalFourthNat.DPay_2487
  · exact WuPaper.ClassicalFourthNat.DPay_2488
  · exact WuPaper.ClassicalFourthNat.DPay_2489
  · exact WuPaper.ClassicalFourthNat.DPay_2490
  · exact WuPaper.ClassicalFourthNat.DPay_2491
  · exact WuPaper.ClassicalFourthNat.DPay_2492
  · exact WuPaper.ClassicalFourthNat.DPay_2493
  · exact WuPaper.ClassicalFourthNat.DPay_2494
  · exact WuPaper.ClassicalFourthNat.DPay_2495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_038
