import WR2GammaHighTailUnitDensity

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighUnit HighUnitSource HighUnitPrimeOutput Real Finset
open scoped Classical

theorem mother_unit_pair_filtered {N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    let p := Wu04RemainingCore.row row
    let W := windows row N
    let R := fun d : ℕ => (N : ℝ) ^ (1/2-δ) / d
    let a0 := fun d => wuLocalCutoff N δ d p.S
    let a1 := fun d => wuLocalCutoff N δ d p.kappa1
    let a2 := fun d => wuLocalCutoff N δ d p.kappa2
    let a3 := fun d => wuLocalCutoff N δ d p.kappa3
    let b := fun d => wuLocalCutoff N δ d p.s
    FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
      FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
      envelope20 N W R (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
      envelope21 N W R (fun _ => 1/p.kappa3) (fun _ => 1/p.s) := by
  let p := Wu04RemainingCore.row row
  have hp := (row_analytic row).mother
  have hs := (row_analytic row).two_lt_s.le
  have hdpos : ∀ d ∈ boxConvolutionSupport (windows row N), 0 < d :=
    fun _ hd => boxConvolutionSupport_pos
      (fun j q hq => (mem_primeWindow.mp hq).1.pos) hd
  have hR : ∀ d ∈ boxConvolutionSupport (windows row N),
      1 < (N : ℝ) ^ (1/2-δ) / d :=
    fun _ hd => (LowerTriple.phi_bounds row hN hδ hδhi hd).2.1
  obtain ⟨h2,h3,hb⟩ := parameter_outer_bounds hp hs
  have h20 := HighUnitPrimeOutput.source_le20 (N := N) (a0 := fun _ => 1/p.S) (a1 := fun _ => 1/p.kappa1)
    (a2 := fun _ => 1/p.kappa2) (a3 := fun _ => 1/p.kappa3) (b := fun _ => 1/p.s)
    hdpos hR (fun _ _ => h2) (fun _ _ => hb)
  have h21 := HighUnitPrimeOutput.source_le21 (N := N) (a0 := fun _ => 1/p.S) (a1 := fun _ => 1/p.kappa1)
    (a2 := fun _ => 1/p.kappa2) (a3 := fun _ => 1/p.kappa3) (b := fun _ => 1/p.s)
    hdpos hR (fun _ _ => h3) (fun _ _ => hb)
  simpa only [wuLocalCutoff] using add_le_add h20 h21

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.mother_unit_pair_filtered
