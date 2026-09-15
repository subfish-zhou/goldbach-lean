import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGroupedActual
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset

/-- Only the two selected primes are counted; the quotient is recovered at fixed E. -/
def fixedCofactorSelected (x : Label) : Fin 2 → ℕ :=
  Fin.cases x.2.1 (fun _ => x.2.2.1)

/-- The original support supplies positive sigma, without assuming a prime output. -/
theorem source_weight_one_le {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (j : Fin 6) {x : Label}
    (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    1 ≤ (sourceFamily N δ Δ V p j).weight x := by
  have hd := (mem_labels x).mp hx |>.1
  change (1 : ℝ) ≤ (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)
  exact_mod_cast mem_boxConvolutionSupport.mp hd

/-- Full ordered convolution multiplicity, including repeated window primes and n=1. -/
theorem source_fixed_cofactor_bound {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 6)
    (hW : ∀ t q, q ∈ convolutionWuWindows N Δ V t →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) (E : ℕ) :
    (∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre E,
      (sourceFamily N δ Δ V p j).weight x) ≤
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+2) := by
  let S := (sourceFamily N δ Δ V p j).layerFibre E
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have hg := source_geometry hN hδ hδhi hb p hp j (mem_filter.mp hx).1
    have he : cofactor x = E := (mem_filter.mp hx).2
    have hE : 0 < E := he ▸ hg.positive
    change (∑ x ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)) ≤ _
    apply HighNonunit.weighted_labels_le _ S (fun x => x.1) fixedCofactorSelected
      hb.1 (by omega) hE (he ▸ hg.le_N)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    · intro a ha
      rw [← (show cofactor a = E from (mem_filter.mp ha).2)]
      exact (cofactor_divisors a).1
    · intro a ha t
      have ham := (mem_filter.mp ha).1
      have hae : cofactor a = E := (mem_filter.mp ha).2
      obtain ⟨hd,hp',hq',_⟩ := (mem_labels a).mp ham
      have hpl := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd hp'
      have hql := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd hq'
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

/-- The threshold precedes N, every box, mother parameter, band and cofactor. -/
theorem source_fixed_cofactor_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6, ∀ E : ℕ,
      (∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre E,
        (sourceFamily N δ Δ V p j).weight x) ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+2) := by
  obtain ⟨T,hT,hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j E
  apply source_fixed_cofactor_bound (by omega) hδ hδhi hb p hp j _ E
  intro t q hq
  have h := hw N hN i Δ V hb t q hq
  exact ⟨h.1,h.2.2⟩

end Wu2008DoubleSieve.LowerTripleGrouped
