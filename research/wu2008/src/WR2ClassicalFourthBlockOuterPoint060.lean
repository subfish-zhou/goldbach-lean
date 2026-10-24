import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint060
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_060 (j : Fin 64) (hj : 64*60+j.val < 10541) :
    OuterPoint (64*60+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3840
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3841
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3842
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3843
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3844
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3845
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3846
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3847
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3848
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3849
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3850
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3851
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3852
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3853
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3854
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3855
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3856
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3857
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3858
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3859
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3860
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3861
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3862
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3863
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3864
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3865
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3866
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3867
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3868
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3869
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3870
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3871
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3872
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3873
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3874
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3875
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3876
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3877
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3878
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3879
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3880
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3881
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3882
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3883
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3884
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3885
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3886
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3887
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3888
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3889
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3890
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3891
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3892
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3893
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3894
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3895
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3896
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3897
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3898
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3899
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3900
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3901
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3902
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_060
