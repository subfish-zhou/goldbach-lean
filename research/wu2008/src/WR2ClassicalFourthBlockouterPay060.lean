import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay060
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_060 (j : Fin 64) (hj : 64*60+j.val < 10540) :
    OuterPay (64*60+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_3840
  · exact WuPaper.ClassicalFourthNat.outerPay_3841
  · exact WuPaper.ClassicalFourthNat.outerPay_3842
  · exact WuPaper.ClassicalFourthNat.outerPay_3843
  · exact WuPaper.ClassicalFourthNat.outerPay_3844
  · exact WuPaper.ClassicalFourthNat.outerPay_3845
  · exact WuPaper.ClassicalFourthNat.outerPay_3846
  · exact WuPaper.ClassicalFourthNat.outerPay_3847
  · exact WuPaper.ClassicalFourthNat.outerPay_3848
  · exact WuPaper.ClassicalFourthNat.outerPay_3849
  · exact WuPaper.ClassicalFourthNat.outerPay_3850
  · exact WuPaper.ClassicalFourthNat.outerPay_3851
  · exact WuPaper.ClassicalFourthNat.outerPay_3852
  · exact WuPaper.ClassicalFourthNat.outerPay_3853
  · exact WuPaper.ClassicalFourthNat.outerPay_3854
  · exact WuPaper.ClassicalFourthNat.outerPay_3855
  · exact WuPaper.ClassicalFourthNat.outerPay_3856
  · exact WuPaper.ClassicalFourthNat.outerPay_3857
  · exact WuPaper.ClassicalFourthNat.outerPay_3858
  · exact WuPaper.ClassicalFourthNat.outerPay_3859
  · exact WuPaper.ClassicalFourthNat.outerPay_3860
  · exact WuPaper.ClassicalFourthNat.outerPay_3861
  · exact WuPaper.ClassicalFourthNat.outerPay_3862
  · exact WuPaper.ClassicalFourthNat.outerPay_3863
  · exact WuPaper.ClassicalFourthNat.outerPay_3864
  · exact WuPaper.ClassicalFourthNat.outerPay_3865
  · exact WuPaper.ClassicalFourthNat.outerPay_3866
  · exact WuPaper.ClassicalFourthNat.outerPay_3867
  · exact WuPaper.ClassicalFourthNat.outerPay_3868
  · exact WuPaper.ClassicalFourthNat.outerPay_3869
  · exact WuPaper.ClassicalFourthNat.outerPay_3870
  · exact WuPaper.ClassicalFourthNat.outerPay_3871
  · exact WuPaper.ClassicalFourthNat.outerPay_3872
  · exact WuPaper.ClassicalFourthNat.outerPay_3873
  · exact WuPaper.ClassicalFourthNat.outerPay_3874
  · exact WuPaper.ClassicalFourthNat.outerPay_3875
  · exact WuPaper.ClassicalFourthNat.outerPay_3876
  · exact WuPaper.ClassicalFourthNat.outerPay_3877
  · exact WuPaper.ClassicalFourthNat.outerPay_3878
  · exact WuPaper.ClassicalFourthNat.outerPay_3879
  · exact WuPaper.ClassicalFourthNat.outerPay_3880
  · exact WuPaper.ClassicalFourthNat.outerPay_3881
  · exact WuPaper.ClassicalFourthNat.outerPay_3882
  · exact WuPaper.ClassicalFourthNat.outerPay_3883
  · exact WuPaper.ClassicalFourthNat.outerPay_3884
  · exact WuPaper.ClassicalFourthNat.outerPay_3885
  · exact WuPaper.ClassicalFourthNat.outerPay_3886
  · exact WuPaper.ClassicalFourthNat.outerPay_3887
  · exact WuPaper.ClassicalFourthNat.outerPay_3888
  · exact WuPaper.ClassicalFourthNat.outerPay_3889
  · exact WuPaper.ClassicalFourthNat.outerPay_3890
  · exact WuPaper.ClassicalFourthNat.outerPay_3891
  · exact WuPaper.ClassicalFourthNat.outerPay_3892
  · exact WuPaper.ClassicalFourthNat.outerPay_3893
  · exact WuPaper.ClassicalFourthNat.outerPay_3894
  · exact WuPaper.ClassicalFourthNat.outerPay_3895
  · exact WuPaper.ClassicalFourthNat.outerPay_3896
  · exact WuPaper.ClassicalFourthNat.outerPay_3897
  · exact WuPaper.ClassicalFourthNat.outerPay_3898
  · exact WuPaper.ClassicalFourthNat.outerPay_3899
  · exact WuPaper.ClassicalFourthNat.outerPay_3900
  · exact WuPaper.ClassicalFourthNat.outerPay_3901
  · exact WuPaper.ClassicalFourthNat.outerPay_3902
  · exact WuPaper.ClassicalFourthNat.outerPay_3903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_060
