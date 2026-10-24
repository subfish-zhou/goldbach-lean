import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay121
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_121 (j : Fin 64) (hj : 64*121+j.val < 10540) :
    OuterPay (64*121+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_7744
  · exact WuPaper.ClassicalFourthNat.outerPay_7745
  · exact WuPaper.ClassicalFourthNat.outerPay_7746
  · exact WuPaper.ClassicalFourthNat.outerPay_7747
  · exact WuPaper.ClassicalFourthNat.outerPay_7748
  · exact WuPaper.ClassicalFourthNat.outerPay_7749
  · exact WuPaper.ClassicalFourthNat.outerPay_7750
  · exact WuPaper.ClassicalFourthNat.outerPay_7751
  · exact WuPaper.ClassicalFourthNat.outerPay_7752
  · exact WuPaper.ClassicalFourthNat.outerPay_7753
  · exact WuPaper.ClassicalFourthNat.outerPay_7754
  · exact WuPaper.ClassicalFourthNat.outerPay_7755
  · exact WuPaper.ClassicalFourthNat.outerPay_7756
  · exact WuPaper.ClassicalFourthNat.outerPay_7757
  · exact WuPaper.ClassicalFourthNat.outerPay_7758
  · exact WuPaper.ClassicalFourthNat.outerPay_7759
  · exact WuPaper.ClassicalFourthNat.outerPay_7760
  · exact WuPaper.ClassicalFourthNat.outerPay_7761
  · exact WuPaper.ClassicalFourthNat.outerPay_7762
  · exact WuPaper.ClassicalFourthNat.outerPay_7763
  · exact WuPaper.ClassicalFourthNat.outerPay_7764
  · exact WuPaper.ClassicalFourthNat.outerPay_7765
  · exact WuPaper.ClassicalFourthNat.outerPay_7766
  · exact WuPaper.ClassicalFourthNat.outerPay_7767
  · exact WuPaper.ClassicalFourthNat.outerPay_7768
  · exact WuPaper.ClassicalFourthNat.outerPay_7769
  · exact WuPaper.ClassicalFourthNat.outerPay_7770
  · exact WuPaper.ClassicalFourthNat.outerPay_7771
  · exact WuPaper.ClassicalFourthNat.outerPay_7772
  · exact WuPaper.ClassicalFourthNat.outerPay_7773
  · exact WuPaper.ClassicalFourthNat.outerPay_7774
  · exact WuPaper.ClassicalFourthNat.outerPay_7775
  · exact WuPaper.ClassicalFourthNat.outerPay_7776
  · exact WuPaper.ClassicalFourthNat.outerPay_7777
  · exact WuPaper.ClassicalFourthNat.outerPay_7778
  · exact WuPaper.ClassicalFourthNat.outerPay_7779
  · exact WuPaper.ClassicalFourthNat.outerPay_7780
  · exact WuPaper.ClassicalFourthNat.outerPay_7781
  · exact WuPaper.ClassicalFourthNat.outerPay_7782
  · exact WuPaper.ClassicalFourthNat.outerPay_7783
  · exact WuPaper.ClassicalFourthNat.outerPay_7784
  · exact WuPaper.ClassicalFourthNat.outerPay_7785
  · exact WuPaper.ClassicalFourthNat.outerPay_7786
  · exact WuPaper.ClassicalFourthNat.outerPay_7787
  · exact WuPaper.ClassicalFourthNat.outerPay_7788
  · exact WuPaper.ClassicalFourthNat.outerPay_7789
  · exact WuPaper.ClassicalFourthNat.outerPay_7790
  · exact WuPaper.ClassicalFourthNat.outerPay_7791
  · exact WuPaper.ClassicalFourthNat.outerPay_7792
  · exact WuPaper.ClassicalFourthNat.outerPay_7793
  · exact WuPaper.ClassicalFourthNat.outerPay_7794
  · exact WuPaper.ClassicalFourthNat.outerPay_7795
  · exact WuPaper.ClassicalFourthNat.outerPay_7796
  · exact WuPaper.ClassicalFourthNat.outerPay_7797
  · exact WuPaper.ClassicalFourthNat.outerPay_7798
  · exact WuPaper.ClassicalFourthNat.outerPay_7799
  · exact WuPaper.ClassicalFourthNat.outerPay_7800
  · exact WuPaper.ClassicalFourthNat.outerPay_7801
  · exact WuPaper.ClassicalFourthNat.outerPay_7802
  · exact WuPaper.ClassicalFourthNat.outerPay_7803
  · exact WuPaper.ClassicalFourthNat.outerPay_7804
  · exact WuPaper.ClassicalFourthNat.outerPay_7805
  · exact WuPaper.ClassicalFourthNat.outerPay_7806
  · exact WuPaper.ClassicalFourthNat.outerPay_7807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_121
