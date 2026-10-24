import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay121
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_121 (j : Fin 64) (hj : 64*121+j.val < 10540) :
    BPay (64*121+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7744
  · exact WuPaper.ClassicalFourthNat.BPay_7745
  · exact WuPaper.ClassicalFourthNat.BPay_7746
  · exact WuPaper.ClassicalFourthNat.BPay_7747
  · exact WuPaper.ClassicalFourthNat.BPay_7748
  · exact WuPaper.ClassicalFourthNat.BPay_7749
  · exact WuPaper.ClassicalFourthNat.BPay_7750
  · exact WuPaper.ClassicalFourthNat.BPay_7751
  · exact WuPaper.ClassicalFourthNat.BPay_7752
  · exact WuPaper.ClassicalFourthNat.BPay_7753
  · exact WuPaper.ClassicalFourthNat.BPay_7754
  · exact WuPaper.ClassicalFourthNat.BPay_7755
  · exact WuPaper.ClassicalFourthNat.BPay_7756
  · exact WuPaper.ClassicalFourthNat.BPay_7757
  · exact WuPaper.ClassicalFourthNat.BPay_7758
  · exact WuPaper.ClassicalFourthNat.BPay_7759
  · exact WuPaper.ClassicalFourthNat.BPay_7760
  · exact WuPaper.ClassicalFourthNat.BPay_7761
  · exact WuPaper.ClassicalFourthNat.BPay_7762
  · exact WuPaper.ClassicalFourthNat.BPay_7763
  · exact WuPaper.ClassicalFourthNat.BPay_7764
  · exact WuPaper.ClassicalFourthNat.BPay_7765
  · exact WuPaper.ClassicalFourthNat.BPay_7766
  · exact WuPaper.ClassicalFourthNat.BPay_7767
  · exact WuPaper.ClassicalFourthNat.BPay_7768
  · exact WuPaper.ClassicalFourthNat.BPay_7769
  · exact WuPaper.ClassicalFourthNat.BPay_7770
  · exact WuPaper.ClassicalFourthNat.BPay_7771
  · exact WuPaper.ClassicalFourthNat.BPay_7772
  · exact WuPaper.ClassicalFourthNat.BPay_7773
  · exact WuPaper.ClassicalFourthNat.BPay_7774
  · exact WuPaper.ClassicalFourthNat.BPay_7775
  · exact WuPaper.ClassicalFourthNat.BPay_7776
  · exact WuPaper.ClassicalFourthNat.BPay_7777
  · exact WuPaper.ClassicalFourthNat.BPay_7778
  · exact WuPaper.ClassicalFourthNat.BPay_7779
  · exact WuPaper.ClassicalFourthNat.BPay_7780
  · exact WuPaper.ClassicalFourthNat.BPay_7781
  · exact WuPaper.ClassicalFourthNat.BPay_7782
  · exact WuPaper.ClassicalFourthNat.BPay_7783
  · exact WuPaper.ClassicalFourthNat.BPay_7784
  · exact WuPaper.ClassicalFourthNat.BPay_7785
  · exact WuPaper.ClassicalFourthNat.BPay_7786
  · exact WuPaper.ClassicalFourthNat.BPay_7787
  · exact WuPaper.ClassicalFourthNat.BPay_7788
  · exact WuPaper.ClassicalFourthNat.BPay_7789
  · exact WuPaper.ClassicalFourthNat.BPay_7790
  · exact WuPaper.ClassicalFourthNat.BPay_7791
  · exact WuPaper.ClassicalFourthNat.BPay_7792
  · exact WuPaper.ClassicalFourthNat.BPay_7793
  · exact WuPaper.ClassicalFourthNat.BPay_7794
  · exact WuPaper.ClassicalFourthNat.BPay_7795
  · exact WuPaper.ClassicalFourthNat.BPay_7796
  · exact WuPaper.ClassicalFourthNat.BPay_7797
  · exact WuPaper.ClassicalFourthNat.BPay_7798
  · exact WuPaper.ClassicalFourthNat.BPay_7799
  · exact WuPaper.ClassicalFourthNat.BPay_7800
  · exact WuPaper.ClassicalFourthNat.BPay_7801
  · exact WuPaper.ClassicalFourthNat.BPay_7802
  · exact WuPaper.ClassicalFourthNat.BPay_7803
  · exact WuPaper.ClassicalFourthNat.BPay_7804
  · exact WuPaper.ClassicalFourthNat.BPay_7805
  · exact WuPaper.ClassicalFourthNat.BPay_7806
  · exact WuPaper.ClassicalFourthNat.BPay_7807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_121
