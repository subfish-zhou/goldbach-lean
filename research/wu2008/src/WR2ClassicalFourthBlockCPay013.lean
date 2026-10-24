import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay013
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_013 (j : Fin 64) (hj : 64*13+j.val < 2540) :
    CPay (64*13+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_832
  · exact WuPaper.ClassicalFourthNat.CPay_833
  · exact WuPaper.ClassicalFourthNat.CPay_834
  · exact WuPaper.ClassicalFourthNat.CPay_835
  · exact WuPaper.ClassicalFourthNat.CPay_836
  · exact WuPaper.ClassicalFourthNat.CPay_837
  · exact WuPaper.ClassicalFourthNat.CPay_838
  · exact WuPaper.ClassicalFourthNat.CPay_839
  · exact WuPaper.ClassicalFourthNat.CPay_840
  · exact WuPaper.ClassicalFourthNat.CPay_841
  · exact WuPaper.ClassicalFourthNat.CPay_842
  · exact WuPaper.ClassicalFourthNat.CPay_843
  · exact WuPaper.ClassicalFourthNat.CPay_844
  · exact WuPaper.ClassicalFourthNat.CPay_845
  · exact WuPaper.ClassicalFourthNat.CPay_846
  · exact WuPaper.ClassicalFourthNat.CPay_847
  · exact WuPaper.ClassicalFourthNat.CPay_848
  · exact WuPaper.ClassicalFourthNat.CPay_849
  · exact WuPaper.ClassicalFourthNat.CPay_850
  · exact WuPaper.ClassicalFourthNat.CPay_851
  · exact WuPaper.ClassicalFourthNat.CPay_852
  · exact WuPaper.ClassicalFourthNat.CPay_853
  · exact WuPaper.ClassicalFourthNat.CPay_854
  · exact WuPaper.ClassicalFourthNat.CPay_855
  · exact WuPaper.ClassicalFourthNat.CPay_856
  · exact WuPaper.ClassicalFourthNat.CPay_857
  · exact WuPaper.ClassicalFourthNat.CPay_858
  · exact WuPaper.ClassicalFourthNat.CPay_859
  · exact WuPaper.ClassicalFourthNat.CPay_860
  · exact WuPaper.ClassicalFourthNat.CPay_861
  · exact WuPaper.ClassicalFourthNat.CPay_862
  · exact WuPaper.ClassicalFourthNat.CPay_863
  · exact WuPaper.ClassicalFourthNat.CPay_864
  · exact WuPaper.ClassicalFourthNat.CPay_865
  · exact WuPaper.ClassicalFourthNat.CPay_866
  · exact WuPaper.ClassicalFourthNat.CPay_867
  · exact WuPaper.ClassicalFourthNat.CPay_868
  · exact WuPaper.ClassicalFourthNat.CPay_869
  · exact WuPaper.ClassicalFourthNat.CPay_870
  · exact WuPaper.ClassicalFourthNat.CPay_871
  · exact WuPaper.ClassicalFourthNat.CPay_872
  · exact WuPaper.ClassicalFourthNat.CPay_873
  · exact WuPaper.ClassicalFourthNat.CPay_874
  · exact WuPaper.ClassicalFourthNat.CPay_875
  · exact WuPaper.ClassicalFourthNat.CPay_876
  · exact WuPaper.ClassicalFourthNat.CPay_877
  · exact WuPaper.ClassicalFourthNat.CPay_878
  · exact WuPaper.ClassicalFourthNat.CPay_879
  · exact WuPaper.ClassicalFourthNat.CPay_880
  · exact WuPaper.ClassicalFourthNat.CPay_881
  · exact WuPaper.ClassicalFourthNat.CPay_882
  · exact WuPaper.ClassicalFourthNat.CPay_883
  · exact WuPaper.ClassicalFourthNat.CPay_884
  · exact WuPaper.ClassicalFourthNat.CPay_885
  · exact WuPaper.ClassicalFourthNat.CPay_886
  · exact WuPaper.ClassicalFourthNat.CPay_887
  · exact WuPaper.ClassicalFourthNat.CPay_888
  · exact WuPaper.ClassicalFourthNat.CPay_889
  · exact WuPaper.ClassicalFourthNat.CPay_890
  · exact WuPaper.ClassicalFourthNat.CPay_891
  · exact WuPaper.ClassicalFourthNat.CPay_892
  · exact WuPaper.ClassicalFourthNat.CPay_893
  · exact WuPaper.ClassicalFourthNat.CPay_894
  · exact WuPaper.ClassicalFourthNat.CPay_895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_013
