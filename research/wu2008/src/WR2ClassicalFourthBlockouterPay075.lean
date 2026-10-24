import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay075
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_075 (j : Fin 64) (hj : 64*75+j.val < 10540) :
    OuterPay (64*75+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_4800
  · exact WuPaper.ClassicalFourthNat.outerPay_4801
  · exact WuPaper.ClassicalFourthNat.outerPay_4802
  · exact WuPaper.ClassicalFourthNat.outerPay_4803
  · exact WuPaper.ClassicalFourthNat.outerPay_4804
  · exact WuPaper.ClassicalFourthNat.outerPay_4805
  · exact WuPaper.ClassicalFourthNat.outerPay_4806
  · exact WuPaper.ClassicalFourthNat.outerPay_4807
  · exact WuPaper.ClassicalFourthNat.outerPay_4808
  · exact WuPaper.ClassicalFourthNat.outerPay_4809
  · exact WuPaper.ClassicalFourthNat.outerPay_4810
  · exact WuPaper.ClassicalFourthNat.outerPay_4811
  · exact WuPaper.ClassicalFourthNat.outerPay_4812
  · exact WuPaper.ClassicalFourthNat.outerPay_4813
  · exact WuPaper.ClassicalFourthNat.outerPay_4814
  · exact WuPaper.ClassicalFourthNat.outerPay_4815
  · exact WuPaper.ClassicalFourthNat.outerPay_4816
  · exact WuPaper.ClassicalFourthNat.outerPay_4817
  · exact WuPaper.ClassicalFourthNat.outerPay_4818
  · exact WuPaper.ClassicalFourthNat.outerPay_4819
  · exact WuPaper.ClassicalFourthNat.outerPay_4820
  · exact WuPaper.ClassicalFourthNat.outerPay_4821
  · exact WuPaper.ClassicalFourthNat.outerPay_4822
  · exact WuPaper.ClassicalFourthNat.outerPay_4823
  · exact WuPaper.ClassicalFourthNat.outerPay_4824
  · exact WuPaper.ClassicalFourthNat.outerPay_4825
  · exact WuPaper.ClassicalFourthNat.outerPay_4826
  · exact WuPaper.ClassicalFourthNat.outerPay_4827
  · exact WuPaper.ClassicalFourthNat.outerPay_4828
  · exact WuPaper.ClassicalFourthNat.outerPay_4829
  · exact WuPaper.ClassicalFourthNat.outerPay_4830
  · exact WuPaper.ClassicalFourthNat.outerPay_4831
  · exact WuPaper.ClassicalFourthNat.outerPay_4832
  · exact WuPaper.ClassicalFourthNat.outerPay_4833
  · exact WuPaper.ClassicalFourthNat.outerPay_4834
  · exact WuPaper.ClassicalFourthNat.outerPay_4835
  · exact WuPaper.ClassicalFourthNat.outerPay_4836
  · exact WuPaper.ClassicalFourthNat.outerPay_4837
  · exact WuPaper.ClassicalFourthNat.outerPay_4838
  · exact WuPaper.ClassicalFourthNat.outerPay_4839
  · exact WuPaper.ClassicalFourthNat.outerPay_4840
  · exact WuPaper.ClassicalFourthNat.outerPay_4841
  · exact WuPaper.ClassicalFourthNat.outerPay_4842
  · exact WuPaper.ClassicalFourthNat.outerPay_4843
  · exact WuPaper.ClassicalFourthNat.outerPay_4844
  · exact WuPaper.ClassicalFourthNat.outerPay_4845
  · exact WuPaper.ClassicalFourthNat.outerPay_4846
  · exact WuPaper.ClassicalFourthNat.outerPay_4847
  · exact WuPaper.ClassicalFourthNat.outerPay_4848
  · exact WuPaper.ClassicalFourthNat.outerPay_4849
  · exact WuPaper.ClassicalFourthNat.outerPay_4850
  · exact WuPaper.ClassicalFourthNat.outerPay_4851
  · exact WuPaper.ClassicalFourthNat.outerPay_4852
  · exact WuPaper.ClassicalFourthNat.outerPay_4853
  · exact WuPaper.ClassicalFourthNat.outerPay_4854
  · exact WuPaper.ClassicalFourthNat.outerPay_4855
  · exact WuPaper.ClassicalFourthNat.outerPay_4856
  · exact WuPaper.ClassicalFourthNat.outerPay_4857
  · exact WuPaper.ClassicalFourthNat.outerPay_4858
  · exact WuPaper.ClassicalFourthNat.outerPay_4859
  · exact WuPaper.ClassicalFourthNat.outerPay_4860
  · exact WuPaper.ClassicalFourthNat.outerPay_4861
  · exact WuPaper.ClassicalFourthNat.outerPay_4862
  · exact WuPaper.ClassicalFourthNat.outerPay_4863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_075
