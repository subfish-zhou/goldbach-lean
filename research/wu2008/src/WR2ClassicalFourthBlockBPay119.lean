import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay119
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_119 (j : Fin 64) (hj : 64*119+j.val < 10540) :
    BPay (64*119+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7616
  · exact WuPaper.ClassicalFourthNat.BPay_7617
  · exact WuPaper.ClassicalFourthNat.BPay_7618
  · exact WuPaper.ClassicalFourthNat.BPay_7619
  · exact WuPaper.ClassicalFourthNat.BPay_7620
  · exact WuPaper.ClassicalFourthNat.BPay_7621
  · exact WuPaper.ClassicalFourthNat.BPay_7622
  · exact WuPaper.ClassicalFourthNat.BPay_7623
  · exact WuPaper.ClassicalFourthNat.BPay_7624
  · exact WuPaper.ClassicalFourthNat.BPay_7625
  · exact WuPaper.ClassicalFourthNat.BPay_7626
  · exact WuPaper.ClassicalFourthNat.BPay_7627
  · exact WuPaper.ClassicalFourthNat.BPay_7628
  · exact WuPaper.ClassicalFourthNat.BPay_7629
  · exact WuPaper.ClassicalFourthNat.BPay_7630
  · exact WuPaper.ClassicalFourthNat.BPay_7631
  · exact WuPaper.ClassicalFourthNat.BPay_7632
  · exact WuPaper.ClassicalFourthNat.BPay_7633
  · exact WuPaper.ClassicalFourthNat.BPay_7634
  · exact WuPaper.ClassicalFourthNat.BPay_7635
  · exact WuPaper.ClassicalFourthNat.BPay_7636
  · exact WuPaper.ClassicalFourthNat.BPay_7637
  · exact WuPaper.ClassicalFourthNat.BPay_7638
  · exact WuPaper.ClassicalFourthNat.BPay_7639
  · exact WuPaper.ClassicalFourthNat.BPay_7640
  · exact WuPaper.ClassicalFourthNat.BPay_7641
  · exact WuPaper.ClassicalFourthNat.BPay_7642
  · exact WuPaper.ClassicalFourthNat.BPay_7643
  · exact WuPaper.ClassicalFourthNat.BPay_7644
  · exact WuPaper.ClassicalFourthNat.BPay_7645
  · exact WuPaper.ClassicalFourthNat.BPay_7646
  · exact WuPaper.ClassicalFourthNat.BPay_7647
  · exact WuPaper.ClassicalFourthNat.BPay_7648
  · exact WuPaper.ClassicalFourthNat.BPay_7649
  · exact WuPaper.ClassicalFourthNat.BPay_7650
  · exact WuPaper.ClassicalFourthNat.BPay_7651
  · exact WuPaper.ClassicalFourthNat.BPay_7652
  · exact WuPaper.ClassicalFourthNat.BPay_7653
  · exact WuPaper.ClassicalFourthNat.BPay_7654
  · exact WuPaper.ClassicalFourthNat.BPay_7655
  · exact WuPaper.ClassicalFourthNat.BPay_7656
  · exact WuPaper.ClassicalFourthNat.BPay_7657
  · exact WuPaper.ClassicalFourthNat.BPay_7658
  · exact WuPaper.ClassicalFourthNat.BPay_7659
  · exact WuPaper.ClassicalFourthNat.BPay_7660
  · exact WuPaper.ClassicalFourthNat.BPay_7661
  · exact WuPaper.ClassicalFourthNat.BPay_7662
  · exact WuPaper.ClassicalFourthNat.BPay_7663
  · exact WuPaper.ClassicalFourthNat.BPay_7664
  · exact WuPaper.ClassicalFourthNat.BPay_7665
  · exact WuPaper.ClassicalFourthNat.BPay_7666
  · exact WuPaper.ClassicalFourthNat.BPay_7667
  · exact WuPaper.ClassicalFourthNat.BPay_7668
  · exact WuPaper.ClassicalFourthNat.BPay_7669
  · exact WuPaper.ClassicalFourthNat.BPay_7670
  · exact WuPaper.ClassicalFourthNat.BPay_7671
  · exact WuPaper.ClassicalFourthNat.BPay_7672
  · exact WuPaper.ClassicalFourthNat.BPay_7673
  · exact WuPaper.ClassicalFourthNat.BPay_7674
  · exact WuPaper.ClassicalFourthNat.BPay_7675
  · exact WuPaper.ClassicalFourthNat.BPay_7676
  · exact WuPaper.ClassicalFourthNat.BPay_7677
  · exact WuPaper.ClassicalFourthNat.BPay_7678
  · exact WuPaper.ClassicalFourthNat.BPay_7679
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_119
