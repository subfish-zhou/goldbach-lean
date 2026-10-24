import WR2GammaHighLowerTripleFibre

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Real Finset
open scoped Classical

/-- One logarithmic remainder bound works for every row and all six physical bands. -/
theorem R1_log_bound {δ A : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ k : Fin 6, ∀ Z : ℝ,
        (sourceFamily j N δ k).R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ C*N/log (N : ℝ)^A := by
  obtain ⟨C,hC,T,hT,hc⟩ := LabelledPhysical.Family.R1_log_saving A highEta
    ((max 1 (1/highEta))^3) hA (by norm_num [highEta]) (by positivity) hd
  refine ⟨C,hC,T,hT,fun N hN j k Z => ?_⟩
  have hN2 : 2 ≤ N := by omega
  apply hc N hN Label (sourceFamily j N δ k) ?_ ?_ ?_ Z
  · intro x hx
    have hg := source_geometry j k hN2 hd hh hx
    exact ⟨hg.power_lower,hg.power_upper⟩
  · intro x hx
    have hm := (mem_labels x).mp hx |>.1
    change (1 : ℝ) ≤ (convolutionCoeff (windows j N) x.1 : ℝ)
    exact_mod_cast mem_boxConvolutionSupport.mp hm
  · exact fixed_cofactor_bound j k hN2 hd hh

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.R1_log_bound
