import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay060
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_060 (j : Fin 64) (hj : 64*60+j.val < 10540) :
    BPay (64*60+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3840
  · exact WuPaper.ClassicalFourthNat.BPay_3841
  · exact WuPaper.ClassicalFourthNat.BPay_3842
  · exact WuPaper.ClassicalFourthNat.BPay_3843
  · exact WuPaper.ClassicalFourthNat.BPay_3844
  · exact WuPaper.ClassicalFourthNat.BPay_3845
  · exact WuPaper.ClassicalFourthNat.BPay_3846
  · exact WuPaper.ClassicalFourthNat.BPay_3847
  · exact WuPaper.ClassicalFourthNat.BPay_3848
  · exact WuPaper.ClassicalFourthNat.BPay_3849
  · exact WuPaper.ClassicalFourthNat.BPay_3850
  · exact WuPaper.ClassicalFourthNat.BPay_3851
  · exact WuPaper.ClassicalFourthNat.BPay_3852
  · exact WuPaper.ClassicalFourthNat.BPay_3853
  · exact WuPaper.ClassicalFourthNat.BPay_3854
  · exact WuPaper.ClassicalFourthNat.BPay_3855
  · exact WuPaper.ClassicalFourthNat.BPay_3856
  · exact WuPaper.ClassicalFourthNat.BPay_3857
  · exact WuPaper.ClassicalFourthNat.BPay_3858
  · exact WuPaper.ClassicalFourthNat.BPay_3859
  · exact WuPaper.ClassicalFourthNat.BPay_3860
  · exact WuPaper.ClassicalFourthNat.BPay_3861
  · exact WuPaper.ClassicalFourthNat.BPay_3862
  · exact WuPaper.ClassicalFourthNat.BPay_3863
  · exact WuPaper.ClassicalFourthNat.BPay_3864
  · exact WuPaper.ClassicalFourthNat.BPay_3865
  · exact WuPaper.ClassicalFourthNat.BPay_3866
  · exact WuPaper.ClassicalFourthNat.BPay_3867
  · exact WuPaper.ClassicalFourthNat.BPay_3868
  · exact WuPaper.ClassicalFourthNat.BPay_3869
  · exact WuPaper.ClassicalFourthNat.BPay_3870
  · exact WuPaper.ClassicalFourthNat.BPay_3871
  · exact WuPaper.ClassicalFourthNat.BPay_3872
  · exact WuPaper.ClassicalFourthNat.BPay_3873
  · exact WuPaper.ClassicalFourthNat.BPay_3874
  · exact WuPaper.ClassicalFourthNat.BPay_3875
  · exact WuPaper.ClassicalFourthNat.BPay_3876
  · exact WuPaper.ClassicalFourthNat.BPay_3877
  · exact WuPaper.ClassicalFourthNat.BPay_3878
  · exact WuPaper.ClassicalFourthNat.BPay_3879
  · exact WuPaper.ClassicalFourthNat.BPay_3880
  · exact WuPaper.ClassicalFourthNat.BPay_3881
  · exact WuPaper.ClassicalFourthNat.BPay_3882
  · exact WuPaper.ClassicalFourthNat.BPay_3883
  · exact WuPaper.ClassicalFourthNat.BPay_3884
  · exact WuPaper.ClassicalFourthNat.BPay_3885
  · exact WuPaper.ClassicalFourthNat.BPay_3886
  · exact WuPaper.ClassicalFourthNat.BPay_3887
  · exact WuPaper.ClassicalFourthNat.BPay_3888
  · exact WuPaper.ClassicalFourthNat.BPay_3889
  · exact WuPaper.ClassicalFourthNat.BPay_3890
  · exact WuPaper.ClassicalFourthNat.BPay_3891
  · exact WuPaper.ClassicalFourthNat.BPay_3892
  · exact WuPaper.ClassicalFourthNat.BPay_3893
  · exact WuPaper.ClassicalFourthNat.BPay_3894
  · exact WuPaper.ClassicalFourthNat.BPay_3895
  · exact WuPaper.ClassicalFourthNat.BPay_3896
  · exact WuPaper.ClassicalFourthNat.BPay_3897
  · exact WuPaper.ClassicalFourthNat.BPay_3898
  · exact WuPaper.ClassicalFourthNat.BPay_3899
  · exact WuPaper.ClassicalFourthNat.BPay_3900
  · exact WuPaper.ClassicalFourthNat.BPay_3901
  · exact WuPaper.ClassicalFourthNat.BPay_3902
  · exact WuPaper.ClassicalFourthNat.BPay_3903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_060
