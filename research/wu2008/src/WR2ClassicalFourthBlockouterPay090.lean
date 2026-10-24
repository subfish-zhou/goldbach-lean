import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay090
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_090 (j : Fin 64) (hj : 64*90+j.val < 10540) :
    OuterPay (64*90+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_5760
  · exact WuPaper.ClassicalFourthNat.outerPay_5761
  · exact WuPaper.ClassicalFourthNat.outerPay_5762
  · exact WuPaper.ClassicalFourthNat.outerPay_5763
  · exact WuPaper.ClassicalFourthNat.outerPay_5764
  · exact WuPaper.ClassicalFourthNat.outerPay_5765
  · exact WuPaper.ClassicalFourthNat.outerPay_5766
  · exact WuPaper.ClassicalFourthNat.outerPay_5767
  · exact WuPaper.ClassicalFourthNat.outerPay_5768
  · exact WuPaper.ClassicalFourthNat.outerPay_5769
  · exact WuPaper.ClassicalFourthNat.outerPay_5770
  · exact WuPaper.ClassicalFourthNat.outerPay_5771
  · exact WuPaper.ClassicalFourthNat.outerPay_5772
  · exact WuPaper.ClassicalFourthNat.outerPay_5773
  · exact WuPaper.ClassicalFourthNat.outerPay_5774
  · exact WuPaper.ClassicalFourthNat.outerPay_5775
  · exact WuPaper.ClassicalFourthNat.outerPay_5776
  · exact WuPaper.ClassicalFourthNat.outerPay_5777
  · exact WuPaper.ClassicalFourthNat.outerPay_5778
  · exact WuPaper.ClassicalFourthNat.outerPay_5779
  · exact WuPaper.ClassicalFourthNat.outerPay_5780
  · exact WuPaper.ClassicalFourthNat.outerPay_5781
  · exact WuPaper.ClassicalFourthNat.outerPay_5782
  · exact WuPaper.ClassicalFourthNat.outerPay_5783
  · exact WuPaper.ClassicalFourthNat.outerPay_5784
  · exact WuPaper.ClassicalFourthNat.outerPay_5785
  · exact WuPaper.ClassicalFourthNat.outerPay_5786
  · exact WuPaper.ClassicalFourthNat.outerPay_5787
  · exact WuPaper.ClassicalFourthNat.outerPay_5788
  · exact WuPaper.ClassicalFourthNat.outerPay_5789
  · exact WuPaper.ClassicalFourthNat.outerPay_5790
  · exact WuPaper.ClassicalFourthNat.outerPay_5791
  · exact WuPaper.ClassicalFourthNat.outerPay_5792
  · exact WuPaper.ClassicalFourthNat.outerPay_5793
  · exact WuPaper.ClassicalFourthNat.outerPay_5794
  · exact WuPaper.ClassicalFourthNat.outerPay_5795
  · exact WuPaper.ClassicalFourthNat.outerPay_5796
  · exact WuPaper.ClassicalFourthNat.outerPay_5797
  · exact WuPaper.ClassicalFourthNat.outerPay_5798
  · exact WuPaper.ClassicalFourthNat.outerPay_5799
  · exact WuPaper.ClassicalFourthNat.outerPay_5800
  · exact WuPaper.ClassicalFourthNat.outerPay_5801
  · exact WuPaper.ClassicalFourthNat.outerPay_5802
  · exact WuPaper.ClassicalFourthNat.outerPay_5803
  · exact WuPaper.ClassicalFourthNat.outerPay_5804
  · exact WuPaper.ClassicalFourthNat.outerPay_5805
  · exact WuPaper.ClassicalFourthNat.outerPay_5806
  · exact WuPaper.ClassicalFourthNat.outerPay_5807
  · exact WuPaper.ClassicalFourthNat.outerPay_5808
  · exact WuPaper.ClassicalFourthNat.outerPay_5809
  · exact WuPaper.ClassicalFourthNat.outerPay_5810
  · exact WuPaper.ClassicalFourthNat.outerPay_5811
  · exact WuPaper.ClassicalFourthNat.outerPay_5812
  · exact WuPaper.ClassicalFourthNat.outerPay_5813
  · exact WuPaper.ClassicalFourthNat.outerPay_5814
  · exact WuPaper.ClassicalFourthNat.outerPay_5815
  · exact WuPaper.ClassicalFourthNat.outerPay_5816
  · exact WuPaper.ClassicalFourthNat.outerPay_5817
  · exact WuPaper.ClassicalFourthNat.outerPay_5818
  · exact WuPaper.ClassicalFourthNat.outerPay_5819
  · exact WuPaper.ClassicalFourthNat.outerPay_5820
  · exact WuPaper.ClassicalFourthNat.outerPay_5821
  · exact WuPaper.ClassicalFourthNat.outerPay_5822
  · exact WuPaper.ClassicalFourthNat.outerPay_5823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_090
