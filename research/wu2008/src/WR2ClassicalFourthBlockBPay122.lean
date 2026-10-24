import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay122
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_122 (j : Fin 64) (hj : 64*122+j.val < 10540) :
    BPay (64*122+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7808
  · exact WuPaper.ClassicalFourthNat.BPay_7809
  · exact WuPaper.ClassicalFourthNat.BPay_7810
  · exact WuPaper.ClassicalFourthNat.BPay_7811
  · exact WuPaper.ClassicalFourthNat.BPay_7812
  · exact WuPaper.ClassicalFourthNat.BPay_7813
  · exact WuPaper.ClassicalFourthNat.BPay_7814
  · exact WuPaper.ClassicalFourthNat.BPay_7815
  · exact WuPaper.ClassicalFourthNat.BPay_7816
  · exact WuPaper.ClassicalFourthNat.BPay_7817
  · exact WuPaper.ClassicalFourthNat.BPay_7818
  · exact WuPaper.ClassicalFourthNat.BPay_7819
  · exact WuPaper.ClassicalFourthNat.BPay_7820
  · exact WuPaper.ClassicalFourthNat.BPay_7821
  · exact WuPaper.ClassicalFourthNat.BPay_7822
  · exact WuPaper.ClassicalFourthNat.BPay_7823
  · exact WuPaper.ClassicalFourthNat.BPay_7824
  · exact WuPaper.ClassicalFourthNat.BPay_7825
  · exact WuPaper.ClassicalFourthNat.BPay_7826
  · exact WuPaper.ClassicalFourthNat.BPay_7827
  · exact WuPaper.ClassicalFourthNat.BPay_7828
  · exact WuPaper.ClassicalFourthNat.BPay_7829
  · exact WuPaper.ClassicalFourthNat.BPay_7830
  · exact WuPaper.ClassicalFourthNat.BPay_7831
  · exact WuPaper.ClassicalFourthNat.BPay_7832
  · exact WuPaper.ClassicalFourthNat.BPay_7833
  · exact WuPaper.ClassicalFourthNat.BPay_7834
  · exact WuPaper.ClassicalFourthNat.BPay_7835
  · exact WuPaper.ClassicalFourthNat.BPay_7836
  · exact WuPaper.ClassicalFourthNat.BPay_7837
  · exact WuPaper.ClassicalFourthNat.BPay_7838
  · exact WuPaper.ClassicalFourthNat.BPay_7839
  · exact WuPaper.ClassicalFourthNat.BPay_7840
  · exact WuPaper.ClassicalFourthNat.BPay_7841
  · exact WuPaper.ClassicalFourthNat.BPay_7842
  · exact WuPaper.ClassicalFourthNat.BPay_7843
  · exact WuPaper.ClassicalFourthNat.BPay_7844
  · exact WuPaper.ClassicalFourthNat.BPay_7845
  · exact WuPaper.ClassicalFourthNat.BPay_7846
  · exact WuPaper.ClassicalFourthNat.BPay_7847
  · exact WuPaper.ClassicalFourthNat.BPay_7848
  · exact WuPaper.ClassicalFourthNat.BPay_7849
  · exact WuPaper.ClassicalFourthNat.BPay_7850
  · exact WuPaper.ClassicalFourthNat.BPay_7851
  · exact WuPaper.ClassicalFourthNat.BPay_7852
  · exact WuPaper.ClassicalFourthNat.BPay_7853
  · exact WuPaper.ClassicalFourthNat.BPay_7854
  · exact WuPaper.ClassicalFourthNat.BPay_7855
  · exact WuPaper.ClassicalFourthNat.BPay_7856
  · exact WuPaper.ClassicalFourthNat.BPay_7857
  · exact WuPaper.ClassicalFourthNat.BPay_7858
  · exact WuPaper.ClassicalFourthNat.BPay_7859
  · exact WuPaper.ClassicalFourthNat.BPay_7860
  · exact WuPaper.ClassicalFourthNat.BPay_7861
  · exact WuPaper.ClassicalFourthNat.BPay_7862
  · exact WuPaper.ClassicalFourthNat.BPay_7863
  · exact WuPaper.ClassicalFourthNat.BPay_7864
  · exact WuPaper.ClassicalFourthNat.BPay_7865
  · exact WuPaper.ClassicalFourthNat.BPay_7866
  · exact WuPaper.ClassicalFourthNat.BPay_7867
  · exact WuPaper.ClassicalFourthNat.BPay_7868
  · exact WuPaper.ClassicalFourthNat.BPay_7869
  · exact WuPaper.ClassicalFourthNat.BPay_7870
  · exact WuPaper.ClassicalFourthNat.BPay_7871
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_122
