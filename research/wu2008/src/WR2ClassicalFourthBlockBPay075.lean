import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay075
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_075 (j : Fin 64) (hj : 64*75+j.val < 10540) :
    BPay (64*75+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4800
  · exact WuPaper.ClassicalFourthNat.BPay_4801
  · exact WuPaper.ClassicalFourthNat.BPay_4802
  · exact WuPaper.ClassicalFourthNat.BPay_4803
  · exact WuPaper.ClassicalFourthNat.BPay_4804
  · exact WuPaper.ClassicalFourthNat.BPay_4805
  · exact WuPaper.ClassicalFourthNat.BPay_4806
  · exact WuPaper.ClassicalFourthNat.BPay_4807
  · exact WuPaper.ClassicalFourthNat.BPay_4808
  · exact WuPaper.ClassicalFourthNat.BPay_4809
  · exact WuPaper.ClassicalFourthNat.BPay_4810
  · exact WuPaper.ClassicalFourthNat.BPay_4811
  · exact WuPaper.ClassicalFourthNat.BPay_4812
  · exact WuPaper.ClassicalFourthNat.BPay_4813
  · exact WuPaper.ClassicalFourthNat.BPay_4814
  · exact WuPaper.ClassicalFourthNat.BPay_4815
  · exact WuPaper.ClassicalFourthNat.BPay_4816
  · exact WuPaper.ClassicalFourthNat.BPay_4817
  · exact WuPaper.ClassicalFourthNat.BPay_4818
  · exact WuPaper.ClassicalFourthNat.BPay_4819
  · exact WuPaper.ClassicalFourthNat.BPay_4820
  · exact WuPaper.ClassicalFourthNat.BPay_4821
  · exact WuPaper.ClassicalFourthNat.BPay_4822
  · exact WuPaper.ClassicalFourthNat.BPay_4823
  · exact WuPaper.ClassicalFourthNat.BPay_4824
  · exact WuPaper.ClassicalFourthNat.BPay_4825
  · exact WuPaper.ClassicalFourthNat.BPay_4826
  · exact WuPaper.ClassicalFourthNat.BPay_4827
  · exact WuPaper.ClassicalFourthNat.BPay_4828
  · exact WuPaper.ClassicalFourthNat.BPay_4829
  · exact WuPaper.ClassicalFourthNat.BPay_4830
  · exact WuPaper.ClassicalFourthNat.BPay_4831
  · exact WuPaper.ClassicalFourthNat.BPay_4832
  · exact WuPaper.ClassicalFourthNat.BPay_4833
  · exact WuPaper.ClassicalFourthNat.BPay_4834
  · exact WuPaper.ClassicalFourthNat.BPay_4835
  · exact WuPaper.ClassicalFourthNat.BPay_4836
  · exact WuPaper.ClassicalFourthNat.BPay_4837
  · exact WuPaper.ClassicalFourthNat.BPay_4838
  · exact WuPaper.ClassicalFourthNat.BPay_4839
  · exact WuPaper.ClassicalFourthNat.BPay_4840
  · exact WuPaper.ClassicalFourthNat.BPay_4841
  · exact WuPaper.ClassicalFourthNat.BPay_4842
  · exact WuPaper.ClassicalFourthNat.BPay_4843
  · exact WuPaper.ClassicalFourthNat.BPay_4844
  · exact WuPaper.ClassicalFourthNat.BPay_4845
  · exact WuPaper.ClassicalFourthNat.BPay_4846
  · exact WuPaper.ClassicalFourthNat.BPay_4847
  · exact WuPaper.ClassicalFourthNat.BPay_4848
  · exact WuPaper.ClassicalFourthNat.BPay_4849
  · exact WuPaper.ClassicalFourthNat.BPay_4850
  · exact WuPaper.ClassicalFourthNat.BPay_4851
  · exact WuPaper.ClassicalFourthNat.BPay_4852
  · exact WuPaper.ClassicalFourthNat.BPay_4853
  · exact WuPaper.ClassicalFourthNat.BPay_4854
  · exact WuPaper.ClassicalFourthNat.BPay_4855
  · exact WuPaper.ClassicalFourthNat.BPay_4856
  · exact WuPaper.ClassicalFourthNat.BPay_4857
  · exact WuPaper.ClassicalFourthNat.BPay_4858
  · exact WuPaper.ClassicalFourthNat.BPay_4859
  · exact WuPaper.ClassicalFourthNat.BPay_4860
  · exact WuPaper.ClassicalFourthNat.BPay_4861
  · exact WuPaper.ClassicalFourthNat.BPay_4862
  · exact WuPaper.ClassicalFourthNat.BPay_4863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_075
