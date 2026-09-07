import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpRough

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Pay the rough-count error with the already proved continuous author kernel bound. -/
theorem g12Sharp_authorRough_kernel_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log (N : ℝ)/N * goldbachG12WeightedRough N (goldbachG12AuthorPrimeWeight N) ≤
        goldbachG12PrimeKernel G12SharpWeight.weight N + δ := by
  let I := goldbachG12PrimeIntegral goldbachG11AuthorWeight
  let B := |I| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let η := δ / B
  have hη : 0 < η := div_pos hδ hB
  obtain ⟨K,hK,hr⟩ := g12Sharp_authorRough_le_kernel η hη
  obtain ⟨L,_,hk⟩ := goldbachG12PrimeKernel_author_le_integral_eventually 1 (by norm_num)
  refine ⟨max K L,hK.trans (le_max_left _ _),?_⟩
  intro N hN
  have hkernel : goldbachG12PrimeKernel goldbachG11AuthorWeight N ≤ B :=
    (hk N (by omega)).trans (add_le_add (le_abs_self I) le_rfl)
  have he : η * goldbachG12PrimeKernel goldbachG11AuthorWeight N ≤ δ := by
    calc
      _ ≤ η * B := mul_le_mul_of_nonneg_left hkernel hη.le
      _ = δ := div_mul_cancel₀ δ hB.ne'
  exact (hr N (by omega)).trans (add_le_add le_rfl he)

/-- The full author-weighted linked source reaches the sharp kernel.
The exceptional r-divides-N term is paid; no extra coprimality is assumed. -/
theorem g12Sharp_authorSource_kernel_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ,
      Real.log (N : ℝ)/N * (400 *
        goldbachG12WeightedSource N ε (goldbachG12AuthorPrimeWeight N)) ≤
          goldbachG12PrimeKernel G12SharpWeight.weight N + δ := by
  obtain ⟨K,hK,hrough⟩ := g12Sharp_authorRough_kernel_budget (δ/2) (half_pos hδ)
  obtain ⟨L,_,hbad⟩ := goldbachG12AuthorBad_normalized_paid (δ/2) (half_pos hδ)
  refine ⟨max K L,hK.trans (le_max_left _ _),?_⟩
  intro N hN ε
  have hN4 : 4 ≤ N := by omega
  have hn : 0 ≤ Real.log (N : ℝ)/N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left (goldbachG12AuthorSource_le_fullRough hN4 ε) hn
  rw [mul_add] at h
  have hr := hrough N (by omega)
  have hb := hbad N (by omega)
  linarith

/-- Actual low physical mother plus eight times the original UNGATED high mass.
The threshold precedes all epsilon, and the target is the literal sharp step prime kernel. -/
theorem g12Sharp_authorLowHigh_kernel_terminal (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ,
      (Real.log (N : ℝ)/N) * 400 * (goldbachG12AuthorLowMotherMass N ε +
        8 * G12ClippedWindow.highMass N ε) ≤
          goldbachG12PrimeKernel G12SharpWeight.weight N + δ := by
  obtain ⟨K,hK,hb⟩ := g12Sharp_authorSource_kernel_budget δ hδ
  refine ⟨K,hK,?_⟩
  intro N hN ε
  have hn : 0 ≤ Real.log (N : ℝ)/N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) (Nat.cast_nonneg _)
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (goldbachG12AuthorLowHigh_le_source (hK.trans hN) ε)
      (by norm_num : (0 : ℝ) ≤ 400)) hn).trans (hb N hN ε)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
