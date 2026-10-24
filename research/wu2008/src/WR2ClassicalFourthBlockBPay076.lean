import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay076
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_076 (j : Fin 64) (hj : 64*76+j.val < 10540) :
    BPay (64*76+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4864
  · exact WuPaper.ClassicalFourthNat.BPay_4865
  · exact WuPaper.ClassicalFourthNat.BPay_4866
  · exact WuPaper.ClassicalFourthNat.BPay_4867
  · exact WuPaper.ClassicalFourthNat.BPay_4868
  · exact WuPaper.ClassicalFourthNat.BPay_4869
  · exact WuPaper.ClassicalFourthNat.BPay_4870
  · exact WuPaper.ClassicalFourthNat.BPay_4871
  · exact WuPaper.ClassicalFourthNat.BPay_4872
  · exact WuPaper.ClassicalFourthNat.BPay_4873
  · exact WuPaper.ClassicalFourthNat.BPay_4874
  · exact WuPaper.ClassicalFourthNat.BPay_4875
  · exact WuPaper.ClassicalFourthNat.BPay_4876
  · exact WuPaper.ClassicalFourthNat.BPay_4877
  · exact WuPaper.ClassicalFourthNat.BPay_4878
  · exact WuPaper.ClassicalFourthNat.BPay_4879
  · exact WuPaper.ClassicalFourthNat.BPay_4880
  · exact WuPaper.ClassicalFourthNat.BPay_4881
  · exact WuPaper.ClassicalFourthNat.BPay_4882
  · exact WuPaper.ClassicalFourthNat.BPay_4883
  · exact WuPaper.ClassicalFourthNat.BPay_4884
  · exact WuPaper.ClassicalFourthNat.BPay_4885
  · exact WuPaper.ClassicalFourthNat.BPay_4886
  · exact WuPaper.ClassicalFourthNat.BPay_4887
  · exact WuPaper.ClassicalFourthNat.BPay_4888
  · exact WuPaper.ClassicalFourthNat.BPay_4889
  · exact WuPaper.ClassicalFourthNat.BPay_4890
  · exact WuPaper.ClassicalFourthNat.BPay_4891
  · exact WuPaper.ClassicalFourthNat.BPay_4892
  · exact WuPaper.ClassicalFourthNat.BPay_4893
  · exact WuPaper.ClassicalFourthNat.BPay_4894
  · exact WuPaper.ClassicalFourthNat.BPay_4895
  · exact WuPaper.ClassicalFourthNat.BPay_4896
  · exact WuPaper.ClassicalFourthNat.BPay_4897
  · exact WuPaper.ClassicalFourthNat.BPay_4898
  · exact WuPaper.ClassicalFourthNat.BPay_4899
  · exact WuPaper.ClassicalFourthNat.BPay_4900
  · exact WuPaper.ClassicalFourthNat.BPay_4901
  · exact WuPaper.ClassicalFourthNat.BPay_4902
  · exact WuPaper.ClassicalFourthNat.BPay_4903
  · exact WuPaper.ClassicalFourthNat.BPay_4904
  · exact WuPaper.ClassicalFourthNat.BPay_4905
  · exact WuPaper.ClassicalFourthNat.BPay_4906
  · exact WuPaper.ClassicalFourthNat.BPay_4907
  · exact WuPaper.ClassicalFourthNat.BPay_4908
  · exact WuPaper.ClassicalFourthNat.BPay_4909
  · exact WuPaper.ClassicalFourthNat.BPay_4910
  · exact WuPaper.ClassicalFourthNat.BPay_4911
  · exact WuPaper.ClassicalFourthNat.BPay_4912
  · exact WuPaper.ClassicalFourthNat.BPay_4913
  · exact WuPaper.ClassicalFourthNat.BPay_4914
  · exact WuPaper.ClassicalFourthNat.BPay_4915
  · exact WuPaper.ClassicalFourthNat.BPay_4916
  · exact WuPaper.ClassicalFourthNat.BPay_4917
  · exact WuPaper.ClassicalFourthNat.BPay_4918
  · exact WuPaper.ClassicalFourthNat.BPay_4919
  · exact WuPaper.ClassicalFourthNat.BPay_4920
  · exact WuPaper.ClassicalFourthNat.BPay_4921
  · exact WuPaper.ClassicalFourthNat.BPay_4922
  · exact WuPaper.ClassicalFourthNat.BPay_4923
  · exact WuPaper.ClassicalFourthNat.BPay_4924
  · exact WuPaper.ClassicalFourthNat.BPay_4925
  · exact WuPaper.ClassicalFourthNat.BPay_4926
  · exact WuPaper.ClassicalFourthNat.BPay_4927
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_076
