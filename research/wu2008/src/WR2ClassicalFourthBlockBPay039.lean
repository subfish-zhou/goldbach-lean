import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay039
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_039 (j : Fin 64) (hj : 64*39+j.val < 10540) :
    BPay (64*39+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2496
  · exact WuPaper.ClassicalFourthNat.BPay_2497
  · exact WuPaper.ClassicalFourthNat.BPay_2498
  · exact WuPaper.ClassicalFourthNat.BPay_2499
  · exact WuPaper.ClassicalFourthNat.BPay_2500
  · exact WuPaper.ClassicalFourthNat.BPay_2501
  · exact WuPaper.ClassicalFourthNat.BPay_2502
  · exact WuPaper.ClassicalFourthNat.BPay_2503
  · exact WuPaper.ClassicalFourthNat.BPay_2504
  · exact WuPaper.ClassicalFourthNat.BPay_2505
  · exact WuPaper.ClassicalFourthNat.BPay_2506
  · exact WuPaper.ClassicalFourthNat.BPay_2507
  · exact WuPaper.ClassicalFourthNat.BPay_2508
  · exact WuPaper.ClassicalFourthNat.BPay_2509
  · exact WuPaper.ClassicalFourthNat.BPay_2510
  · exact WuPaper.ClassicalFourthNat.BPay_2511
  · exact WuPaper.ClassicalFourthNat.BPay_2512
  · exact WuPaper.ClassicalFourthNat.BPay_2513
  · exact WuPaper.ClassicalFourthNat.BPay_2514
  · exact WuPaper.ClassicalFourthNat.BPay_2515
  · exact WuPaper.ClassicalFourthNat.BPay_2516
  · exact WuPaper.ClassicalFourthNat.BPay_2517
  · exact WuPaper.ClassicalFourthNat.BPay_2518
  · exact WuPaper.ClassicalFourthNat.BPay_2519
  · exact WuPaper.ClassicalFourthNat.BPay_2520
  · exact WuPaper.ClassicalFourthNat.BPay_2521
  · exact WuPaper.ClassicalFourthNat.BPay_2522
  · exact WuPaper.ClassicalFourthNat.BPay_2523
  · exact WuPaper.ClassicalFourthNat.BPay_2524
  · exact WuPaper.ClassicalFourthNat.BPay_2525
  · exact WuPaper.ClassicalFourthNat.BPay_2526
  · exact WuPaper.ClassicalFourthNat.BPay_2527
  · exact WuPaper.ClassicalFourthNat.BPay_2528
  · exact WuPaper.ClassicalFourthNat.BPay_2529
  · exact WuPaper.ClassicalFourthNat.BPay_2530
  · exact WuPaper.ClassicalFourthNat.BPay_2531
  · exact WuPaper.ClassicalFourthNat.BPay_2532
  · exact WuPaper.ClassicalFourthNat.BPay_2533
  · exact WuPaper.ClassicalFourthNat.BPay_2534
  · exact WuPaper.ClassicalFourthNat.BPay_2535
  · exact WuPaper.ClassicalFourthNat.BPay_2536
  · exact WuPaper.ClassicalFourthNat.BPay_2537
  · exact WuPaper.ClassicalFourthNat.BPay_2538
  · exact WuPaper.ClassicalFourthNat.BPay_2539
  · exact WuPaper.ClassicalFourthNat.BPay_2540
  · exact WuPaper.ClassicalFourthNat.BPay_2541
  · exact WuPaper.ClassicalFourthNat.BPay_2542
  · exact WuPaper.ClassicalFourthNat.BPay_2543
  · exact WuPaper.ClassicalFourthNat.BPay_2544
  · exact WuPaper.ClassicalFourthNat.BPay_2545
  · exact WuPaper.ClassicalFourthNat.BPay_2546
  · exact WuPaper.ClassicalFourthNat.BPay_2547
  · exact WuPaper.ClassicalFourthNat.BPay_2548
  · exact WuPaper.ClassicalFourthNat.BPay_2549
  · exact WuPaper.ClassicalFourthNat.BPay_2550
  · exact WuPaper.ClassicalFourthNat.BPay_2551
  · exact WuPaper.ClassicalFourthNat.BPay_2552
  · exact WuPaper.ClassicalFourthNat.BPay_2553
  · exact WuPaper.ClassicalFourthNat.BPay_2554
  · exact WuPaper.ClassicalFourthNat.BPay_2555
  · exact WuPaper.ClassicalFourthNat.BPay_2556
  · exact WuPaper.ClassicalFourthNat.BPay_2557
  · exact WuPaper.ClassicalFourthNat.BPay_2558
  · exact WuPaper.ClassicalFourthNat.BPay_2559
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_039
