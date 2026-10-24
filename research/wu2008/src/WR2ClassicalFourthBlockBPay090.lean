import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay090
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_090 (j : Fin 64) (hj : 64*90+j.val < 10540) :
    BPay (64*90+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5760
  · exact WuPaper.ClassicalFourthNat.BPay_5761
  · exact WuPaper.ClassicalFourthNat.BPay_5762
  · exact WuPaper.ClassicalFourthNat.BPay_5763
  · exact WuPaper.ClassicalFourthNat.BPay_5764
  · exact WuPaper.ClassicalFourthNat.BPay_5765
  · exact WuPaper.ClassicalFourthNat.BPay_5766
  · exact WuPaper.ClassicalFourthNat.BPay_5767
  · exact WuPaper.ClassicalFourthNat.BPay_5768
  · exact WuPaper.ClassicalFourthNat.BPay_5769
  · exact WuPaper.ClassicalFourthNat.BPay_5770
  · exact WuPaper.ClassicalFourthNat.BPay_5771
  · exact WuPaper.ClassicalFourthNat.BPay_5772
  · exact WuPaper.ClassicalFourthNat.BPay_5773
  · exact WuPaper.ClassicalFourthNat.BPay_5774
  · exact WuPaper.ClassicalFourthNat.BPay_5775
  · exact WuPaper.ClassicalFourthNat.BPay_5776
  · exact WuPaper.ClassicalFourthNat.BPay_5777
  · exact WuPaper.ClassicalFourthNat.BPay_5778
  · exact WuPaper.ClassicalFourthNat.BPay_5779
  · exact WuPaper.ClassicalFourthNat.BPay_5780
  · exact WuPaper.ClassicalFourthNat.BPay_5781
  · exact WuPaper.ClassicalFourthNat.BPay_5782
  · exact WuPaper.ClassicalFourthNat.BPay_5783
  · exact WuPaper.ClassicalFourthNat.BPay_5784
  · exact WuPaper.ClassicalFourthNat.BPay_5785
  · exact WuPaper.ClassicalFourthNat.BPay_5786
  · exact WuPaper.ClassicalFourthNat.BPay_5787
  · exact WuPaper.ClassicalFourthNat.BPay_5788
  · exact WuPaper.ClassicalFourthNat.BPay_5789
  · exact WuPaper.ClassicalFourthNat.BPay_5790
  · exact WuPaper.ClassicalFourthNat.BPay_5791
  · exact WuPaper.ClassicalFourthNat.BPay_5792
  · exact WuPaper.ClassicalFourthNat.BPay_5793
  · exact WuPaper.ClassicalFourthNat.BPay_5794
  · exact WuPaper.ClassicalFourthNat.BPay_5795
  · exact WuPaper.ClassicalFourthNat.BPay_5796
  · exact WuPaper.ClassicalFourthNat.BPay_5797
  · exact WuPaper.ClassicalFourthNat.BPay_5798
  · exact WuPaper.ClassicalFourthNat.BPay_5799
  · exact WuPaper.ClassicalFourthNat.BPay_5800
  · exact WuPaper.ClassicalFourthNat.BPay_5801
  · exact WuPaper.ClassicalFourthNat.BPay_5802
  · exact WuPaper.ClassicalFourthNat.BPay_5803
  · exact WuPaper.ClassicalFourthNat.BPay_5804
  · exact WuPaper.ClassicalFourthNat.BPay_5805
  · exact WuPaper.ClassicalFourthNat.BPay_5806
  · exact WuPaper.ClassicalFourthNat.BPay_5807
  · exact WuPaper.ClassicalFourthNat.BPay_5808
  · exact WuPaper.ClassicalFourthNat.BPay_5809
  · exact WuPaper.ClassicalFourthNat.BPay_5810
  · exact WuPaper.ClassicalFourthNat.BPay_5811
  · exact WuPaper.ClassicalFourthNat.BPay_5812
  · exact WuPaper.ClassicalFourthNat.BPay_5813
  · exact WuPaper.ClassicalFourthNat.BPay_5814
  · exact WuPaper.ClassicalFourthNat.BPay_5815
  · exact WuPaper.ClassicalFourthNat.BPay_5816
  · exact WuPaper.ClassicalFourthNat.BPay_5817
  · exact WuPaper.ClassicalFourthNat.BPay_5818
  · exact WuPaper.ClassicalFourthNat.BPay_5819
  · exact WuPaper.ClassicalFourthNat.BPay_5820
  · exact WuPaper.ClassicalFourthNat.BPay_5821
  · exact WuPaper.ClassicalFourthNat.BPay_5822
  · exact WuPaper.ClassicalFourthNat.BPay_5823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_090
