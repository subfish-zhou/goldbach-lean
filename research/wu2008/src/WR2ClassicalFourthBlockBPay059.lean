import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay059
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_059 (j : Fin 64) (hj : 64*59+j.val < 10540) :
    BPay (64*59+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3776
  · exact WuPaper.ClassicalFourthNat.BPay_3777
  · exact WuPaper.ClassicalFourthNat.BPay_3778
  · exact WuPaper.ClassicalFourthNat.BPay_3779
  · exact WuPaper.ClassicalFourthNat.BPay_3780
  · exact WuPaper.ClassicalFourthNat.BPay_3781
  · exact WuPaper.ClassicalFourthNat.BPay_3782
  · exact WuPaper.ClassicalFourthNat.BPay_3783
  · exact WuPaper.ClassicalFourthNat.BPay_3784
  · exact WuPaper.ClassicalFourthNat.BPay_3785
  · exact WuPaper.ClassicalFourthNat.BPay_3786
  · exact WuPaper.ClassicalFourthNat.BPay_3787
  · exact WuPaper.ClassicalFourthNat.BPay_3788
  · exact WuPaper.ClassicalFourthNat.BPay_3789
  · exact WuPaper.ClassicalFourthNat.BPay_3790
  · exact WuPaper.ClassicalFourthNat.BPay_3791
  · exact WuPaper.ClassicalFourthNat.BPay_3792
  · exact WuPaper.ClassicalFourthNat.BPay_3793
  · exact WuPaper.ClassicalFourthNat.BPay_3794
  · exact WuPaper.ClassicalFourthNat.BPay_3795
  · exact WuPaper.ClassicalFourthNat.BPay_3796
  · exact WuPaper.ClassicalFourthNat.BPay_3797
  · exact WuPaper.ClassicalFourthNat.BPay_3798
  · exact WuPaper.ClassicalFourthNat.BPay_3799
  · exact WuPaper.ClassicalFourthNat.BPay_3800
  · exact WuPaper.ClassicalFourthNat.BPay_3801
  · exact WuPaper.ClassicalFourthNat.BPay_3802
  · exact WuPaper.ClassicalFourthNat.BPay_3803
  · exact WuPaper.ClassicalFourthNat.BPay_3804
  · exact WuPaper.ClassicalFourthNat.BPay_3805
  · exact WuPaper.ClassicalFourthNat.BPay_3806
  · exact WuPaper.ClassicalFourthNat.BPay_3807
  · exact WuPaper.ClassicalFourthNat.BPay_3808
  · exact WuPaper.ClassicalFourthNat.BPay_3809
  · exact WuPaper.ClassicalFourthNat.BPay_3810
  · exact WuPaper.ClassicalFourthNat.BPay_3811
  · exact WuPaper.ClassicalFourthNat.BPay_3812
  · exact WuPaper.ClassicalFourthNat.BPay_3813
  · exact WuPaper.ClassicalFourthNat.BPay_3814
  · exact WuPaper.ClassicalFourthNat.BPay_3815
  · exact WuPaper.ClassicalFourthNat.BPay_3816
  · exact WuPaper.ClassicalFourthNat.BPay_3817
  · exact WuPaper.ClassicalFourthNat.BPay_3818
  · exact WuPaper.ClassicalFourthNat.BPay_3819
  · exact WuPaper.ClassicalFourthNat.BPay_3820
  · exact WuPaper.ClassicalFourthNat.BPay_3821
  · exact WuPaper.ClassicalFourthNat.BPay_3822
  · exact WuPaper.ClassicalFourthNat.BPay_3823
  · exact WuPaper.ClassicalFourthNat.BPay_3824
  · exact WuPaper.ClassicalFourthNat.BPay_3825
  · exact WuPaper.ClassicalFourthNat.BPay_3826
  · exact WuPaper.ClassicalFourthNat.BPay_3827
  · exact WuPaper.ClassicalFourthNat.BPay_3828
  · exact WuPaper.ClassicalFourthNat.BPay_3829
  · exact WuPaper.ClassicalFourthNat.BPay_3830
  · exact WuPaper.ClassicalFourthNat.BPay_3831
  · exact WuPaper.ClassicalFourthNat.BPay_3832
  · exact WuPaper.ClassicalFourthNat.BPay_3833
  · exact WuPaper.ClassicalFourthNat.BPay_3834
  · exact WuPaper.ClassicalFourthNat.BPay_3835
  · exact WuPaper.ClassicalFourthNat.BPay_3836
  · exact WuPaper.ClassicalFourthNat.BPay_3837
  · exact WuPaper.ClassicalFourthNat.BPay_3838
  · exact WuPaper.ClassicalFourthNat.BPay_3839
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_059
