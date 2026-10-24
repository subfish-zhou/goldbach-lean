import WR2GammaHighLowerTripleGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFixedCofactor

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Finset
open scoped Classical

theorem fixed_cofactor_bound {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (E : ℕ) :
    (∑ x ∈ (sourceFamily j N δ k).layerFibre E,
      (sourceFamily j N δ k).weight x) ≤ (max 1 (1/highEta))^3 := by
  let S := (sourceFamily j N δ k).layerFibre E
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have hg := source_geometry j k hN hδ hδhi (mem_filter.mp hx).1
    have he : cofactor x = E := (mem_filter.mp hx).2
    have hE : 0 < E := he ▸ hg.positive
    change (∑ x ∈ S, (convolutionCoeff (windows j N) x.1 : ℝ)) ≤ _
    apply HighNonunit.weighted_labels_le _ S (fun x => x.1) fixedCofactorSelected
      (by norm_num : 1 ≤ 1) (by omega : 1 < N) hE (he ▸ hg.le_N)
      (by norm_num [highEta] : 0 < highEta) (fun t q hq => by
        have h := prime_geometry j hN hδ hδhi hq
        exact ⟨h.1,h.2.2.1⟩)
    · intro a ha
      rw [← (show cofactor a = E from (mem_filter.mp ha).2)]
      exact (cofactor_divisors a).1
    · intro a ha t
      have ham := (mem_filter.mp ha).1
      have hae : cofactor a = E := (mem_filter.mp ha).2
      obtain ⟨hd,hp',hq',_⟩ := (mem_labels a).mp ham
      have hpl := window_lower j hN hδ hδhi hd hp'
      have hql := window_lower j hN hδ hδhi hd hq'
      have hpd : a.2.1 ∣ E := hae ▸ (cofactor_divisors a).2.1
      have hqd : a.2.2.1 ∣ E := hae ▸ (cofactor_divisors a).2.2
      refine Fin.cases ?_ (fun t => ?_) t
      · exact ⟨hpl.1,hpd,hpl.2⟩
      · exact ⟨hql.1,hqd,hql.2⟩
    · intro a ha b hb' hd ht
      apply fixedE_projection_injective hE (mem_filter.mp ha).2 (mem_filter.mp hb').2
      have hp' : a.2.1 = b.2.1 := congr_fun ht 0
      have hq' : a.2.2.1 = b.2.2.1 := congr_fun ht 1
      exact Prod.ext hd (Prod.ext hp' hq')
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity


end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.fixed_cofactor_bound
