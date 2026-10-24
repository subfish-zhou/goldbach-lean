import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay013
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_013 (j : Fin 64) (hj : 64*13+j.val < 2540) :
    DPay (64*13+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_832
  · exact WuPaper.ClassicalFourthNat.DPay_833
  · exact WuPaper.ClassicalFourthNat.DPay_834
  · exact WuPaper.ClassicalFourthNat.DPay_835
  · exact WuPaper.ClassicalFourthNat.DPay_836
  · exact WuPaper.ClassicalFourthNat.DPay_837
  · exact WuPaper.ClassicalFourthNat.DPay_838
  · exact WuPaper.ClassicalFourthNat.DPay_839
  · exact WuPaper.ClassicalFourthNat.DPay_840
  · exact WuPaper.ClassicalFourthNat.DPay_841
  · exact WuPaper.ClassicalFourthNat.DPay_842
  · exact WuPaper.ClassicalFourthNat.DPay_843
  · exact WuPaper.ClassicalFourthNat.DPay_844
  · exact WuPaper.ClassicalFourthNat.DPay_845
  · exact WuPaper.ClassicalFourthNat.DPay_846
  · exact WuPaper.ClassicalFourthNat.DPay_847
  · exact WuPaper.ClassicalFourthNat.DPay_848
  · exact WuPaper.ClassicalFourthNat.DPay_849
  · exact WuPaper.ClassicalFourthNat.DPay_850
  · exact WuPaper.ClassicalFourthNat.DPay_851
  · exact WuPaper.ClassicalFourthNat.DPay_852
  · exact WuPaper.ClassicalFourthNat.DPay_853
  · exact WuPaper.ClassicalFourthNat.DPay_854
  · exact WuPaper.ClassicalFourthNat.DPay_855
  · exact WuPaper.ClassicalFourthNat.DPay_856
  · exact WuPaper.ClassicalFourthNat.DPay_857
  · exact WuPaper.ClassicalFourthNat.DPay_858
  · exact WuPaper.ClassicalFourthNat.DPay_859
  · exact WuPaper.ClassicalFourthNat.DPay_860
  · exact WuPaper.ClassicalFourthNat.DPay_861
  · exact WuPaper.ClassicalFourthNat.DPay_862
  · exact WuPaper.ClassicalFourthNat.DPay_863
  · exact WuPaper.ClassicalFourthNat.DPay_864
  · exact WuPaper.ClassicalFourthNat.DPay_865
  · exact WuPaper.ClassicalFourthNat.DPay_866
  · exact WuPaper.ClassicalFourthNat.DPay_867
  · exact WuPaper.ClassicalFourthNat.DPay_868
  · exact WuPaper.ClassicalFourthNat.DPay_869
  · exact WuPaper.ClassicalFourthNat.DPay_870
  · exact WuPaper.ClassicalFourthNat.DPay_871
  · exact WuPaper.ClassicalFourthNat.DPay_872
  · exact WuPaper.ClassicalFourthNat.DPay_873
  · exact WuPaper.ClassicalFourthNat.DPay_874
  · exact WuPaper.ClassicalFourthNat.DPay_875
  · exact WuPaper.ClassicalFourthNat.DPay_876
  · exact WuPaper.ClassicalFourthNat.DPay_877
  · exact WuPaper.ClassicalFourthNat.DPay_878
  · exact WuPaper.ClassicalFourthNat.DPay_879
  · exact WuPaper.ClassicalFourthNat.DPay_880
  · exact WuPaper.ClassicalFourthNat.DPay_881
  · exact WuPaper.ClassicalFourthNat.DPay_882
  · exact WuPaper.ClassicalFourthNat.DPay_883
  · exact WuPaper.ClassicalFourthNat.DPay_884
  · exact WuPaper.ClassicalFourthNat.DPay_885
  · exact WuPaper.ClassicalFourthNat.DPay_886
  · exact WuPaper.ClassicalFourthNat.DPay_887
  · exact WuPaper.ClassicalFourthNat.DPay_888
  · exact WuPaper.ClassicalFourthNat.DPay_889
  · exact WuPaper.ClassicalFourthNat.DPay_890
  · exact WuPaper.ClassicalFourthNat.DPay_891
  · exact WuPaper.ClassicalFourthNat.DPay_892
  · exact WuPaper.ClassicalFourthNat.DPay_893
  · exact WuPaper.ClassicalFourthNat.DPay_894
  · exact WuPaper.ClassicalFourthNat.DPay_895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_013
