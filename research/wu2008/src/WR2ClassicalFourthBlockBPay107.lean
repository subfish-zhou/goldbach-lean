import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay107
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_107 (j : Fin 64) (hj : 64*107+j.val < 10540) :
    BPay (64*107+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6848
  · exact WuPaper.ClassicalFourthNat.BPay_6849
  · exact WuPaper.ClassicalFourthNat.BPay_6850
  · exact WuPaper.ClassicalFourthNat.BPay_6851
  · exact WuPaper.ClassicalFourthNat.BPay_6852
  · exact WuPaper.ClassicalFourthNat.BPay_6853
  · exact WuPaper.ClassicalFourthNat.BPay_6854
  · exact WuPaper.ClassicalFourthNat.BPay_6855
  · exact WuPaper.ClassicalFourthNat.BPay_6856
  · exact WuPaper.ClassicalFourthNat.BPay_6857
  · exact WuPaper.ClassicalFourthNat.BPay_6858
  · exact WuPaper.ClassicalFourthNat.BPay_6859
  · exact WuPaper.ClassicalFourthNat.BPay_6860
  · exact WuPaper.ClassicalFourthNat.BPay_6861
  · exact WuPaper.ClassicalFourthNat.BPay_6862
  · exact WuPaper.ClassicalFourthNat.BPay_6863
  · exact WuPaper.ClassicalFourthNat.BPay_6864
  · exact WuPaper.ClassicalFourthNat.BPay_6865
  · exact WuPaper.ClassicalFourthNat.BPay_6866
  · exact WuPaper.ClassicalFourthNat.BPay_6867
  · exact WuPaper.ClassicalFourthNat.BPay_6868
  · exact WuPaper.ClassicalFourthNat.BPay_6869
  · exact WuPaper.ClassicalFourthNat.BPay_6870
  · exact WuPaper.ClassicalFourthNat.BPay_6871
  · exact WuPaper.ClassicalFourthNat.BPay_6872
  · exact WuPaper.ClassicalFourthNat.BPay_6873
  · exact WuPaper.ClassicalFourthNat.BPay_6874
  · exact WuPaper.ClassicalFourthNat.BPay_6875
  · exact WuPaper.ClassicalFourthNat.BPay_6876
  · exact WuPaper.ClassicalFourthNat.BPay_6877
  · exact WuPaper.ClassicalFourthNat.BPay_6878
  · exact WuPaper.ClassicalFourthNat.BPay_6879
  · exact WuPaper.ClassicalFourthNat.BPay_6880
  · exact WuPaper.ClassicalFourthNat.BPay_6881
  · exact WuPaper.ClassicalFourthNat.BPay_6882
  · exact WuPaper.ClassicalFourthNat.BPay_6883
  · exact WuPaper.ClassicalFourthNat.BPay_6884
  · exact WuPaper.ClassicalFourthNat.BPay_6885
  · exact WuPaper.ClassicalFourthNat.BPay_6886
  · exact WuPaper.ClassicalFourthNat.BPay_6887
  · exact WuPaper.ClassicalFourthNat.BPay_6888
  · exact WuPaper.ClassicalFourthNat.BPay_6889
  · exact WuPaper.ClassicalFourthNat.BPay_6890
  · exact WuPaper.ClassicalFourthNat.BPay_6891
  · exact WuPaper.ClassicalFourthNat.BPay_6892
  · exact WuPaper.ClassicalFourthNat.BPay_6893
  · exact WuPaper.ClassicalFourthNat.BPay_6894
  · exact WuPaper.ClassicalFourthNat.BPay_6895
  · exact WuPaper.ClassicalFourthNat.BPay_6896
  · exact WuPaper.ClassicalFourthNat.BPay_6897
  · exact WuPaper.ClassicalFourthNat.BPay_6898
  · exact WuPaper.ClassicalFourthNat.BPay_6899
  · exact WuPaper.ClassicalFourthNat.BPay_6900
  · exact WuPaper.ClassicalFourthNat.BPay_6901
  · exact WuPaper.ClassicalFourthNat.BPay_6902
  · exact WuPaper.ClassicalFourthNat.BPay_6903
  · exact WuPaper.ClassicalFourthNat.BPay_6904
  · exact WuPaper.ClassicalFourthNat.BPay_6905
  · exact WuPaper.ClassicalFourthNat.BPay_6906
  · exact WuPaper.ClassicalFourthNat.BPay_6907
  · exact WuPaper.ClassicalFourthNat.BPay_6908
  · exact WuPaper.ClassicalFourthNat.BPay_6909
  · exact WuPaper.ClassicalFourthNat.BPay_6910
  · exact WuPaper.ClassicalFourthNat.BPay_6911
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_107
