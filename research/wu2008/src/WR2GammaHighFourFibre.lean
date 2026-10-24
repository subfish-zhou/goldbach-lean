import WR2GammaHighFourSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSieveMultiplicity

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Finset
open scoped Classical

theorem actual_profile_data {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 4) {x : Gamma16Profile}
    (hx : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k) :
    (∀ r, (selected x r).Prime ∧
      (N : ℝ)^(highEta) ≤ (selected x r : ℝ)) ∧
    0 < x.1*x.2.2.2.1*x.2.2.1*x.2.1 ∧
    0 < gamma16Cofactor x ∧ gamma16Cofactor x ≤ N := by
  obtain ⟨hd,h3,h2,h1,_,hn,_,_,_,_,hcap⟩ := profile_data hx
  have g1 := LowerTriple.window_lower j hN hδ hδhi hd h1
  have g2 := LowerTriple.window_lower j hN hδ hδhi hd h2
  have g3 := LowerTriple.window_lower j hN hδ hδhi hd h3
  have hdpos := boxConvolutionSupport_pos (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hd
  refine ⟨?_, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos g1.1.pos) g2.1.pos) g3.1.pos,
    ?_, (Nat.le_mul_of_pos_right _ g3.1.pos).trans hcap⟩
  · intro r
    fin_cases r
    · exact g1
    · exact g2
    · exact g3
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos (by omega))
      g1.1.pos) g2.1.pos) g3.1.pos

theorem actual_fixed_cofactor {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 4)
    (hW : ∀ r q, q ∈ windows j N r →
      q.Prime ∧ (N : ℝ)^(highEta) ≤ (q : ℝ)) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k).filter
      (fun x => gamma16Cofactor x = e),
      (convolutionCoeff (windows j N) x.1 : ℝ)) ≤
      (max 1 (1/(highEta)))^4 := by
  let S := (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k).filter
    (fun x => gamma16Cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have gx := actual_profile_data j hN hδ hδhi k (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    apply HighNonunit.weighted_labels_le _ S (fun x => x.1) selected (by norm_num : 1 ≤ 1) (by omega)
      (he ▸ gx.2.2.1) (he ▸ gx.2.2.2)
      (by norm_num [highEta] : 0 < highEta) hW
    · intro a ha
      rw [← (mem_filter.mp ha).2]
      exact (((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
        (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    · intro a ha r
      have ga := actual_profile_data j hN hδ hδhi k (mem_filter.mp ha).1
      exact ⟨(ga.1 r).1, (mem_filter.mp ha).2 ▸ selected_dvd a r, (ga.1 r).2⟩
    · intro a ha b hb' hd ht
      have ga := actual_profile_data j hN hδ hδhi k (mem_filter.mp ha).1
      exact profile_recover hd ht ga.2.1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm)
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

/-- Restricting to physical labels preserves the full cofactor multiplicity bound. -/
theorem fixed_cofactor_bound {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (E : ℕ) :
    (∑ x ∈ (sourceFamily j N δ k).layerFibre E,
      (sourceFamily j N δ k).weight x) ≤ (max 1 (1/highEta))^4 := by
  have hfull := actual_fixed_cofactor j hN hd hh k (fun _ q hq => by
    have hg := prime_geometry j hN hd hh hq
    exact ⟨hg.1,hg.2.2.1⟩) E
  apply le_trans _ hfull
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩
  · intro x _ _
    exact Nat.cast_nonneg _

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.fixed_cofactor_bound
