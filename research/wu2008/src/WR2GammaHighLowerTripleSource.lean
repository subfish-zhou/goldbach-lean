import WR2GammaHighPairGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGroupedActual

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve WuSource.SrcSingle LowerTripleGrouped Finset
open scoped Classical

def sourceMass (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  LowerTripleGrouped.sourceMass N (windows j N)
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)
    (fun d => (actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1)
    (fun d => (actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.2)
    (actualPre N δ (Wu04RemainingCore.row j) k)

def sourceFamily (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : LabelledPhysical.Family Label N :=
  family N (windows j N)
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)
    (fun d => (actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1)
    (fun d => (actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.2)
    (actualPre N δ (Wu04RemainingCore.row j) k)
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hd)

/-- The six original bands retain their own strict ordering and prefix masks. -/
theorem original_dictionary {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    gamma j N δ (10+k.val) = sourceMass j N δ k := by
  unfold gamma secondFunctionalMotherGammaSum sourceMass LowerTripleGrouped.sourceMass
  apply sum_congr rfl
  intro d hm
  obtain ⟨hab,hbc,hce,hef⟩ := high_cutoffs j hN hd hh hm
  fin_cases k
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    rw [secondFunctionalMother_gamma10_ordered_source N d N hab hbc hce hef]
    simp [actualPre, actualBands, bands, and_assoc]
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    rw [secondFunctionalMother_gamma11_ordered_source N d N hab hbc hce hef]
    simp [actualPre, actualBands, bands, and_assoc]
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    rw [secondFunctionalMother_gamma12_ordered_source N d N hab hbc hce hef]
    simp [actualPre, actualBands, bands, and_assoc]
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    rw [secondFunctionalMother_gamma13_ordered_source N d N hab hbc hce hef]
    simp [actualPre, actualBands, bands, and_assoc]
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    rw [secondFunctionalMother_gamma14_ordered_source N d N hab hbc hce hef]
    simp [actualPre, actualBands, bands, and_assoc]
  · norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    rw [secondFunctionalMother_gamma15_ordered_source N d N hab hbc hce hef]
    simp [actualPre, actualBands, bands, and_assoc]

/-- Each actual Gamma term is bounded by its own labelled physical prime mass. -/
theorem actual_source_upper {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    gamma j N δ (10+k.val) ≤ (sourceFamily j N δ k).primeMass := by
  rw [original_dictionary j k (by omega) hd hh]
  exact LowerTripleGrouped.source_upper _ hN he

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.actual_source_upper
