import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFixedCofactor
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleSieveSmall
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorPayment

namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset Real
open scoped Classical

/-- The full original cofactor mask implies roughness relative to N, including n=1. -/
theorem source_relative_rough {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 6)
    (hW : ∀ a q, q ∈ convolutionWuWindows N Δ V a →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ))
    {x : Label} (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    ∀ r, r.Prime → r ∣ cofactor x → r.Coprime N →
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (r : ℝ) := by
  obtain ⟨hd,hp',hq',_⟩ := (mem_labels x).mp hx
  have hpl := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd hp'
  have hql := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd hq'
  apply RelativeRoughness.of_sifted (source_mask p j hx).2 hql.2
  intro r hr hrd hc
  rcases hr.dvd_mul.mp hrd with hdp | hNr
  · rcases hr.dvd_mul.mp hdp with hdv | hpv
    · exact omega3_support_prime_lower _ hW hd hr hdv
    · have he : r = x.2.1 := ((Nat.dvd_prime hpl.1).mp hpv).resolve_left hr.ne_one
      simpa only [he] using hpl.2
  · exact (hr.coprime_iff_not_dvd.mp hc hNr).elim

/-- Actual relative roughness, full sigma layers and closed Small share one threshold. -/
theorem source_error_inputs (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let η := wuLocalExponent k δ / 10
      let H := max 1 (1/η)
      (∀ j : Fin 6,
        let L := sourceFamily N δ Δ V p j
        (∀ x ∈ L.labels, ∀ q, q.Prime → q ∣ L.cofactor x → q.Coprime N →
          (N : ℝ)^η ≤ (q : ℝ)) ∧
        (∀ e, (∑ x ∈ L.labels.filter (fun x => L.cofactor x = e), L.weight x) ≤ H^(k+2))) ∧
      (∀ Z : ℝ, 0 ≤ Z →
        (∑ j : Fin 6, LowerTripleGroupedOutput.closedSmall N δ Δ V p j Z) ≤ 6*H^(k+3)*Z) := by
  obtain ⟨T0,hT0,hm⟩ := source_fixed_cofactor_uniform k hδ hδhi
  obtain ⟨T1,_,hs⟩ := LowerTripleGroupedOutput.source_all_small k hδ hδhi
  obtain ⟨T2,_,hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  have h0 := (le_max_left T0 (max T1 T2)).trans hN
  have h1 := (le_max_left T1 T2).trans ((le_max_right T0 (max T1 T2)).trans hN)
  have h2 := (le_max_right T1 T2).trans ((le_max_right T0 (max T1 T2)).trans hN)
  have hW : ∀ a q, q ∈ convolutionWuWindows N Δ V a →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) :=
    fun a q hq => ⟨(hw N h2 i Δ V hb a q hq).1, (hw N h2 i Δ V hb a q hq).2.2⟩
  refine ⟨?_, (hs N h1 i Δ V hb p hp).2.1⟩
  intro j
  exact ⟨fun x hx => source_relative_rough (by omega) hδ hδhi hb p hp j hW hx,
    hm N h0 i Δ V hb p hp j⟩

end Wu2008DoubleSieve.LowerTripleGrouped
