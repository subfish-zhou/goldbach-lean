import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint013
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_013 (j : Fin 64) (hj : 64*13+j.val < 10541) :
    OuterPoint (64*13+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_832
  · exact WuPaper.ClassicalFourthNat.OuterPoint_833
  · exact WuPaper.ClassicalFourthNat.OuterPoint_834
  · exact WuPaper.ClassicalFourthNat.OuterPoint_835
  · exact WuPaper.ClassicalFourthNat.OuterPoint_836
  · exact WuPaper.ClassicalFourthNat.OuterPoint_837
  · exact WuPaper.ClassicalFourthNat.OuterPoint_838
  · exact WuPaper.ClassicalFourthNat.OuterPoint_839
  · exact WuPaper.ClassicalFourthNat.OuterPoint_840
  · exact WuPaper.ClassicalFourthNat.OuterPoint_841
  · exact WuPaper.ClassicalFourthNat.OuterPoint_842
  · exact WuPaper.ClassicalFourthNat.OuterPoint_843
  · exact WuPaper.ClassicalFourthNat.OuterPoint_844
  · exact WuPaper.ClassicalFourthNat.OuterPoint_845
  · exact WuPaper.ClassicalFourthNat.OuterPoint_846
  · exact WuPaper.ClassicalFourthNat.OuterPoint_847
  · exact WuPaper.ClassicalFourthNat.OuterPoint_848
  · exact WuPaper.ClassicalFourthNat.OuterPoint_849
  · exact WuPaper.ClassicalFourthNat.OuterPoint_850
  · exact WuPaper.ClassicalFourthNat.OuterPoint_851
  · exact WuPaper.ClassicalFourthNat.OuterPoint_852
  · exact WuPaper.ClassicalFourthNat.OuterPoint_853
  · exact WuPaper.ClassicalFourthNat.OuterPoint_854
  · exact WuPaper.ClassicalFourthNat.OuterPoint_855
  · exact WuPaper.ClassicalFourthNat.OuterPoint_856
  · exact WuPaper.ClassicalFourthNat.OuterPoint_857
  · exact WuPaper.ClassicalFourthNat.OuterPoint_858
  · exact WuPaper.ClassicalFourthNat.OuterPoint_859
  · exact WuPaper.ClassicalFourthNat.OuterPoint_860
  · exact WuPaper.ClassicalFourthNat.OuterPoint_861
  · exact WuPaper.ClassicalFourthNat.OuterPoint_862
  · exact WuPaper.ClassicalFourthNat.OuterPoint_863
  · exact WuPaper.ClassicalFourthNat.OuterPoint_864
  · exact WuPaper.ClassicalFourthNat.OuterPoint_865
  · exact WuPaper.ClassicalFourthNat.OuterPoint_866
  · exact WuPaper.ClassicalFourthNat.OuterPoint_867
  · exact WuPaper.ClassicalFourthNat.OuterPoint_868
  · exact WuPaper.ClassicalFourthNat.OuterPoint_869
  · exact WuPaper.ClassicalFourthNat.OuterPoint_870
  · exact WuPaper.ClassicalFourthNat.OuterPoint_871
  · exact WuPaper.ClassicalFourthNat.OuterPoint_872
  · exact WuPaper.ClassicalFourthNat.OuterPoint_873
  · exact WuPaper.ClassicalFourthNat.OuterPoint_874
  · exact WuPaper.ClassicalFourthNat.OuterPoint_875
  · exact WuPaper.ClassicalFourthNat.OuterPoint_876
  · exact WuPaper.ClassicalFourthNat.OuterPoint_877
  · exact WuPaper.ClassicalFourthNat.OuterPoint_878
  · exact WuPaper.ClassicalFourthNat.OuterPoint_879
  · exact WuPaper.ClassicalFourthNat.OuterPoint_880
  · exact WuPaper.ClassicalFourthNat.OuterPoint_881
  · exact WuPaper.ClassicalFourthNat.OuterPoint_882
  · exact WuPaper.ClassicalFourthNat.OuterPoint_883
  · exact WuPaper.ClassicalFourthNat.OuterPoint_884
  · exact WuPaper.ClassicalFourthNat.OuterPoint_885
  · exact WuPaper.ClassicalFourthNat.OuterPoint_886
  · exact WuPaper.ClassicalFourthNat.OuterPoint_887
  · exact WuPaper.ClassicalFourthNat.OuterPoint_888
  · exact WuPaper.ClassicalFourthNat.OuterPoint_889
  · exact WuPaper.ClassicalFourthNat.OuterPoint_890
  · exact WuPaper.ClassicalFourthNat.OuterPoint_891
  · exact WuPaper.ClassicalFourthNat.OuterPoint_892
  · exact WuPaper.ClassicalFourthNat.OuterPoint_893
  · exact WuPaper.ClassicalFourthNat.OuterPoint_894
  · exact WuPaper.ClassicalFourthNat.OuterPoint_895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_013
