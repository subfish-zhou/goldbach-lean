import WR2GammaHighTailUnitFamily

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighBoxRecovery Finset
open scoped Classical

theorem fixed_cofactor_bound {n N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)))
    (j : Fin n) (b : ℕ → ℝ) (e : ℕ) :
    (∑ c ∈ (family N (windows row N) P j b).filter (fun c => cofactor c = e),
      (convolutionCoeff (windows row N) c.1 : ℝ)) ≤ (max 1 (1/highEta))^(1+n) := by
  let S := (family N (windows row N) P j b).filter (fun c => cofactor c = e)
  by_cases hn : S.Nonempty
  · obtain ⟨c,hc⟩ := hn
    obtain ⟨hc,he⟩ := mem_filter.mp hc
    have hg := source_profile_geometry row hN hd hh P j b hc
    apply weighted_fibre_le _ _ (by norm_num : 1 ≤ 1) (by omega)
      (he ▸ hg.positive) (he ▸ hg.le_N) (by norm_num [highEta] : 0 < highEta)
    · intro a q hq
      have hw := prime_geometry row hN hd hh hq
      exact ⟨hw.1,hw.2.2.1⟩
    · exact fun _ hc => (mem_filter.mp hc).2
    · intro c hc t
      obtain ⟨hc,he⟩ := mem_filter.mp hc
      have ht := (source_profile_geometry row hN hd hh P j b hc).selected_large t
      exact ⟨ht.1,he ▸ ht.2.1,ht.2.2⟩
  · change (∑ c ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hn, sum_empty]
    positivity

theorem family_facts {n N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)))
    (j : Fin n) (b : ℕ → ℝ) :
    FamilyFacts 1 N highEta (windows row N) (family N (windows row N) P j b) j b := by
  refine ⟨?_,fixed_cofactor_bound row hN hd hh P j b⟩
  intro c hc
  refine ⟨source_profile_geometry row hN hd hh P j b hc,?_⟩
  apply source_profile_rough row hN hd hh ?_ c (mem_family.mp hc).1
  intro a q hq
  have hw := prime_geometry row hN hd hh hq
  exact ⟨hw.1,hw.2.2.1⟩

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.family_facts
