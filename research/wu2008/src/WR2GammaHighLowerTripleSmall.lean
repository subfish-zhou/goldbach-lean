import WR2GammaHighLowerTripleOutput

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Finset
open scoped Classical

/-- The original weighted sum with a closed real cutoff; no endpoint atom is removed. -/
def closedSmall (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) (Z : ℝ) : ℝ :=
  ∑ x ∈ (sourceFamily j N δ k).labels,
    (convolutionCoeff (windows j N) x.1 : ℝ) *
      ((outputFibre j N δ k x).filter
        (fun r => ((N-cofactor x*r : ℕ) : ℝ) ≤ Z)).card

/-- Primality supplies the lower endpoint even when the fibre is empty. -/
theorem small_card_disintegration (j : Fin 3) (N Z : ℕ) (δ : ℝ) (k : Fin 6) (x : Label) :
    (∑ ell ∈ Icc 1 Z, ((outputFibre j N δ k x).filter
      (fun r => N-cofactor x*r = ell)).card) =
      ((outputFibre j N δ k x).filter (fun r => N-cofactor x*r ≤ Z)).card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext r
  simp only [mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · intro h
    have hp : (N-cofactor x*r).Prime := (mem_filter.mp h.1).2
    exact ⟨h.1,hp.pos,h.2⟩

/-- Exact exchange of the label and output sums, using the closed natural floor. -/
theorem closedSmall_disintegration (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) {Z : ℝ} (hZ : 0 ≤ Z) :
    closedSmall j N δ k Z =
      ∑ ell ∈ Icc 1 ⌊Z⌋₊, ∑ x ∈ (sourceFamily j N δ k).labels,
        (convolutionCoeff (windows j N) x.1 : ℝ) *
          ((outputFibre j N δ k x).filter (fun r => N-cofactor x*r = ell)).card := by
  rw [sum_comm]
  unfold closedSmall
  apply sum_congr rfl
  intro x _
  rw [← mul_sum, ← Nat.cast_sum, small_card_disintegration]
  simp only [Nat.le_floor_iff hZ]

/-- Pay each integer output once, rather than once per label. -/
theorem closedSmall_le_of_output_bound {N : ℕ} {δ C Z : ℝ} (j : Fin 3) (k : Fin 6) (hZ : 0 ≤ Z) (hC : 0 ≤ C)
    (h : ∀ ell, (∑ x ∈ (sourceFamily j N δ k).labels,
      (convolutionCoeff (windows j N) x.1 : ℝ) *
        ((outputFibre j N δ k x).filter (fun r => N-cofactor x*r = ell)).card) ≤ C) :
    closedSmall j N δ k Z ≤ C*Z := by
  rw [closedSmall_disintegration j N δ k hZ]
  calc
    _ ≤ ∑ _ell ∈ Icc 1 ⌊Z⌋₊, C := sum_le_sum (fun ell _ => h ell)
    _ = C*(⌊Z⌋₊ : ℝ) := by simp [mul_comm]
    _ ≤ C*Z := mul_le_mul_of_nonneg_left (Nat.floor_le hZ) hC

/-- The actual Family.small uses a strict upper cutoff, hence only a one-sided bridge. -/
theorem source_small_le_closed (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) (Z : ℝ) :
    (sourceFamily j N δ k).small Z ≤ closedSmall j N δ k Z := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro r hr
  obtain ⟨hr,hprime,hlt⟩ := mem_filter.mp hr
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hr,hprime⟩,hlt.le⟩

theorem small_bound {N : ℕ} {δ Z : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (hZ : 0 ≤ Z) :
    (sourceFamily j N δ k).small Z ≤ (max 1 (1/highEta))^4*Z :=
  (source_small_le_closed j N δ k Z).trans
    (closedSmall_le_of_output_bound j k hZ (by positivity) (actual_fixed_output j k hN hd hh))

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.small_bound
