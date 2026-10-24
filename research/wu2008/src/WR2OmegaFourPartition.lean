import WSrcSingleCount

/-! Exact insertion of all four adjacent first-functional high windows. -/
noncomputable section
namespace WuPaper.R2OmegaFour
open Wu2008DoubleSieve WuSource.SrcSingle
open scoped BigOperators

theorem four_window_partition {N : ℕ} (hN : 2 ≤ N) :
    (∑ j : Fin 4, psiCount (Fin.natAdd 3 j) N) =
      primeBlock N (sevenBoundary 7) (sevenBoundary 3) := by
  have h1 := prime_block_add (N := N) hN
    (seven_boundary_step (k := 6) (by omega)) (seven_boundary_step (k := 5) (by omega))
  have h2 := prime_block_add (N := N) hN
    ((seven_boundary_step (k := 6) (by omega)).trans (seven_boundary_step (k := 5) (by omega)))
    (seven_boundary_step (k := 4) (by omega))
  have h3 := prime_block_add (N := N) hN
    (((seven_boundary_step (k := 6) (by omega)).trans
      (seven_boundary_step (k := 5) (by omega))).trans (seven_boundary_step (k := 4) (by omega)))
    (seven_boundary_step (k := 3) (by omega))
  simp only [Fin.sum_univ_succ, psi_count_eq_block]
  norm_num only [Fin.val_natAdd, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, add_zero]
  linarith only [h1, h2, h3]

theorem high_count_partition {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) :
    SingleUpperHighQuadrature.highCount N δ (1/3) =
      SingleUpperHighQuadrature.highCount N δ (sevenBoundary 7) +
      (∑ j : Fin 4, psiCount (Fin.natAdd 3 j) N) + HighSix.U3tailCount N := by
  rw [four_window_partition hN]
  have htail : HighSix.U3tailCount N = primeBlock N (sevenBoundary 3) (1/3) := by
    have hb : sevenBoundary 3 = HighSix.right := by
      norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha, HighSix.right]
    rw [hb]
    rfl
  rw [htail]
  unfold SingleUpperHighQuadrature.highCount
  rw [HighSix.highPrimes_window hN hδhi, HighSix.highPrimes_window hN hδhi]
  change primeBlock N ((1/2-δ)/2) (1/3) =
    primeBlock N ((1/2-δ)/2) (sevenBoundary 7) +
      primeBlock N (sevenBoundary 7) (sevenBoundary 3) +
      primeBlock N (sevenBoundary 3) (1/3)
  have hc : (1/2-δ)/2 ≤ sevenBoundary 7 := by
    norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]
    linarith
  have h73 : sevenBoundary 7 ≤ sevenBoundary 3 := by
    norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]
  have h3 : sevenBoundary 3 ≤ (1/3 : ℝ) := by
    norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]
  rw [prime_block_add hN hc h73, prime_block_add hN (hc.trans h73) h3]

end WuPaper.R2OmegaFour
#print axioms WuPaper.R2OmegaFour.high_count_partition
