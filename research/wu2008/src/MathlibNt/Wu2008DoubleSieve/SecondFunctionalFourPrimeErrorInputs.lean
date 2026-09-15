import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSieveSmall
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitRelative
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorPayment

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real
open scoped Classical

/-- Original weighted sigma and relative roughness, with no caller-side geometric gate. -/
theorem source_error_inputs (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let η := wuLocalExponent k δ / 10
      let H := max 1 (1/η)
      (∀ j : Fin 4,
        let L := sourceFamily N δ Δ V p j
        (∀ x ∈ L.labels, ∀ q, q.Prime → q ∣ L.cofactor x → q.Coprime N →
          (N : ℝ)^η ≤ (q : ℝ)) ∧
        (∀ e, (∑ x ∈ L.labels.filter (fun x => L.cofactor x = e), L.weight x) ≤ H^(k+3))) ∧
      (∀ Z : ℝ, 0 ≤ Z →
        (∑ j : Fin 4, closedSmall N δ p (convolutionWuWindows N Δ V) j Z) ≤
          4*H^(k+4)*Z) := by
  obtain ⟨T0,hT0,hm⟩ := source_all_multiplicities k hδ hδhi
  obtain ⟨T1,_,hu⟩ := actual_family_uniform k hδ hδhi
  refine ⟨max T0 T1, hT0.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp
  have hm' := hm N ((le_max_left _ _).trans hN) i Δ V hb p hp
  have hu' := hu N ((le_max_right _ _).trans hN) i Δ V hb p hp
  refine ⟨?_, hm'.2.1⟩
  intro j
  exact ⟨fun x hx => ((hu' j).2.2 x hx).2.2, (hm'.1 j).2.2.1⟩

end Wu2008DoubleSieve.FourPrimeNonunit
