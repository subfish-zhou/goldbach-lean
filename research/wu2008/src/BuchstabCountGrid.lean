import BuchstabCountCutoff

namespace BuchstabCount
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- Exact decomposition of the original Buchstab count into the literal
occupied cells. The d*N prime domain and p cutoff are not replaced. -/
theorem buchstab_occupied_exact {N r : ℕ} {δ Δ s : ℝ} {V : Fin 2 → ℝ}
    (hN : 0 < N) (hΔ : 1 < Δ) (hV : ∀ j, 0 < V j)
    (hQ : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      1 ≤ (N : ℝ)^(1/2-δ)/d)
    (hs : 2 ≤ s) (hs3 : s ≤ 3)
    (hrhi : ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s) <
      reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 (r+1)) :
    wuBoxPhi N δ (convolutionWuWindows N Δ V) 3 =
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s +
      ∑ j ∈ InsertedGain.occupiedCells N δ Δ V s r,
        ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d 3) (wuLocalCutoff N δ d s) ∩
            HighOmega2.cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 j,
            (sourceSieveCount N (d*p) ((d*p)*N) (p : ℝ) : ℝ) := by
  rw [wuBoxPhi_buchstab _ hQ (by linarith) hs3]
  congr 1
  let J := InsertedGain.occupiedCells N δ Δ V s r
  let P := fun d => primeWindow (d*N) (wuLocalCutoff N δ d 3) (wuLocalCutoff N δ d s)
  let C := HighOmega2.cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3
  let F := fun d p => (sourceSieveCount N (d*p) ((d*p)*N) (p : ℝ) : ℝ)
  have split (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      ∑ p ∈ P d, F d p = ∑ j ∈ J, ∑ p ∈ P d ∩ C j, F d p := by
    calc
      _ = ∑ p ∈ P d, ∑ j ∈ J, if p ∈ C j then F d p else 0 := by
        apply sum_congr rfl
        intro p hp
        have hpN := selected_prime_window_subset N d _ _ hp
        obtain ⟨j,hj,hunique⟩ := HighOmega2.complete_cover hN hΔ hV hs hs3 hrhi d hd p hpN
        have hjJ : j ∈ J := mem_filter.mpr ⟨mem_range.mpr hj.1,d,hd,p,hpN,hj.2⟩
        symm
        rw [sum_eq_single_of_mem j hjJ]
        · simp only [C, if_pos hj.2]
        · intro k hk hkj
          have hk0 : k < r+2 := mem_range.mp (mem_filter.mp hk).1
          have hn : p ∉ C k := fun hpk => hkj (hunique k ⟨hk0,hpk⟩)
          simp only [if_neg hn]
      _ = ∑ j ∈ J, ∑ p ∈ P d, if p ∈ C j then F d p else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro j _
        rw [← sum_filter]
        congr 1
  calc
    _ = ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ j ∈ J, ∑ p ∈ P d ∩ C j, F d p := by
      apply sum_congr rfl
      intro d hd
      rw [split d hd]
    _ = _ := by
      simp only [mul_sum]
      exact sum_comm

/-- Every clipped actual source count is bounded by the full inserted Phi.
The full labelled fibre is retained, including repeated prime labels. -/
theorem clipped_cell_le_phi (N j : ℕ) (δ Δ s : ℝ) (V : Fin 2 → ℝ)
    (hΔ : 0 < Δ) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d 3) (wuLocalCutoff N δ d s) ∩
        HighOmega2.cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 j,
        (sourceSieveCount N (d*p) ((d*p)*N) (p : ℝ) : ℝ)) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ
        (Fin.cons (reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 (j+1)) V)) (29/10) := by
  rw [convolutionWuWindows_cons, ← HighOmega2.cell_as_window N j _ Δ 3 hΔ, wuBoxPhi_cons]
  apply sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply le_trans (sum_le_sum (fun p hp => ?_))
  · apply sum_le_sum_of_subset_of_nonneg inter_subset_right
    intro p _ _
    unfold sourceSieveCount
    positivity
  · have hp' := mem_primeWindow.mp (mem_inter.mp hp).1
    exact_mod_cast sourceSieveCount_antitone N (d*p) ((d*p)*N)
      (inserted_cutoff_le_prime hp'.1 hp'.2.2.1)

end
end BuchstabCount
