import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint121
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_121 (j : Fin 64) (hj : 64*121+j.val < 10541) :
    OuterPoint (64*121+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7744
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7745
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7746
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7747
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7748
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7749
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7750
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7751
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7752
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7753
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7754
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7755
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7756
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7757
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7758
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7759
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7760
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7761
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7762
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7763
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7764
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7765
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7766
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7767
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7768
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7769
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7770
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7771
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7772
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7773
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7774
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7775
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7776
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7777
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7778
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7779
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7780
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7781
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7782
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7783
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7784
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7785
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7786
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7787
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7788
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7789
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7790
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7791
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7792
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7793
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7794
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7795
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7796
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7797
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7798
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7799
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7800
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7801
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7802
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7803
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7804
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7805
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7806
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_121
