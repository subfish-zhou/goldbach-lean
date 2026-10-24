import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay088
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_088 (j : Fin 64) (hj : 64*88+j.val < 10540) :
    BPay (64*88+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5632
  · exact WuPaper.ClassicalFourthNat.BPay_5633
  · exact WuPaper.ClassicalFourthNat.BPay_5634
  · exact WuPaper.ClassicalFourthNat.BPay_5635
  · exact WuPaper.ClassicalFourthNat.BPay_5636
  · exact WuPaper.ClassicalFourthNat.BPay_5637
  · exact WuPaper.ClassicalFourthNat.BPay_5638
  · exact WuPaper.ClassicalFourthNat.BPay_5639
  · exact WuPaper.ClassicalFourthNat.BPay_5640
  · exact WuPaper.ClassicalFourthNat.BPay_5641
  · exact WuPaper.ClassicalFourthNat.BPay_5642
  · exact WuPaper.ClassicalFourthNat.BPay_5643
  · exact WuPaper.ClassicalFourthNat.BPay_5644
  · exact WuPaper.ClassicalFourthNat.BPay_5645
  · exact WuPaper.ClassicalFourthNat.BPay_5646
  · exact WuPaper.ClassicalFourthNat.BPay_5647
  · exact WuPaper.ClassicalFourthNat.BPay_5648
  · exact WuPaper.ClassicalFourthNat.BPay_5649
  · exact WuPaper.ClassicalFourthNat.BPay_5650
  · exact WuPaper.ClassicalFourthNat.BPay_5651
  · exact WuPaper.ClassicalFourthNat.BPay_5652
  · exact WuPaper.ClassicalFourthNat.BPay_5653
  · exact WuPaper.ClassicalFourthNat.BPay_5654
  · exact WuPaper.ClassicalFourthNat.BPay_5655
  · exact WuPaper.ClassicalFourthNat.BPay_5656
  · exact WuPaper.ClassicalFourthNat.BPay_5657
  · exact WuPaper.ClassicalFourthNat.BPay_5658
  · exact WuPaper.ClassicalFourthNat.BPay_5659
  · exact WuPaper.ClassicalFourthNat.BPay_5660
  · exact WuPaper.ClassicalFourthNat.BPay_5661
  · exact WuPaper.ClassicalFourthNat.BPay_5662
  · exact WuPaper.ClassicalFourthNat.BPay_5663
  · exact WuPaper.ClassicalFourthNat.BPay_5664
  · exact WuPaper.ClassicalFourthNat.BPay_5665
  · exact WuPaper.ClassicalFourthNat.BPay_5666
  · exact WuPaper.ClassicalFourthNat.BPay_5667
  · exact WuPaper.ClassicalFourthNat.BPay_5668
  · exact WuPaper.ClassicalFourthNat.BPay_5669
  · exact WuPaper.ClassicalFourthNat.BPay_5670
  · exact WuPaper.ClassicalFourthNat.BPay_5671
  · exact WuPaper.ClassicalFourthNat.BPay_5672
  · exact WuPaper.ClassicalFourthNat.BPay_5673
  · exact WuPaper.ClassicalFourthNat.BPay_5674
  · exact WuPaper.ClassicalFourthNat.BPay_5675
  · exact WuPaper.ClassicalFourthNat.BPay_5676
  · exact WuPaper.ClassicalFourthNat.BPay_5677
  · exact WuPaper.ClassicalFourthNat.BPay_5678
  · exact WuPaper.ClassicalFourthNat.BPay_5679
  · exact WuPaper.ClassicalFourthNat.BPay_5680
  · exact WuPaper.ClassicalFourthNat.BPay_5681
  · exact WuPaper.ClassicalFourthNat.BPay_5682
  · exact WuPaper.ClassicalFourthNat.BPay_5683
  · exact WuPaper.ClassicalFourthNat.BPay_5684
  · exact WuPaper.ClassicalFourthNat.BPay_5685
  · exact WuPaper.ClassicalFourthNat.BPay_5686
  · exact WuPaper.ClassicalFourthNat.BPay_5687
  · exact WuPaper.ClassicalFourthNat.BPay_5688
  · exact WuPaper.ClassicalFourthNat.BPay_5689
  · exact WuPaper.ClassicalFourthNat.BPay_5690
  · exact WuPaper.ClassicalFourthNat.BPay_5691
  · exact WuPaper.ClassicalFourthNat.BPay_5692
  · exact WuPaper.ClassicalFourthNat.BPay_5693
  · exact WuPaper.ClassicalFourthNat.BPay_5694
  · exact WuPaper.ClassicalFourthNat.BPay_5695
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_088
