import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitActualFamily

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical

/-- Relative roughness uses exactly the original mask, not global residual roughness. -/
theorem actual_source_relative {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 4)
    (hW : ∀ a q, q ∈ convolutionWuWindows N Δ V a →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ))
    {x : Gamma16Profile}
    (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j) :
    ∀ r, r.Prime → r ∣ gamma16Cofactor x → r.Coprime N →
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (r : ℝ) := by
  obtain ⟨hd,h3,h2,h1,_,_,hs,_⟩ := profile_data hx
  have hp3 := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd h3
  have hp2 := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd h2
  have hp1 := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd h1
  have hs' : Sifted (x.1 * [x.2.2.2.1,x.2.2.1].prod * N) x.2.2.2.2 x.2.1 := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hs
  have hpre := RelativeRoughness.masked_prefix [x.2.2.2.1,x.2.2.1] hs' hp3.2
    (fun r hr hrd => omega3_support_prime_lower _ hW hd hr hrd)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp1
      · exact hp2)
  have hlast : ∀ r : ℕ, r.Prime → r ∣ x.2.1 → r.Coprime N →
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (r : ℝ) := by
    intro r hr hrd _
    have heq : r = x.2.1 := ((Nat.dvd_prime hp3.1).mp hrd).resolve_left hr.ne_one
    simpa only [heq] using hp3.2
  have hfull := RelativeRoughness.mul hpre hlast
  simpa only [gamma16Cofactor, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using hfull

/-- The common threshold precedes N, boxes, mother parameters and all four words. -/
theorem actual_family_uniform (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      let L := sourceFamily N δ Δ V p j
      L.primeMass = actualEnvelope N δ p (convolutionWuWindows N Δ V) j ∧
      L.mass = actualRawMass N δ p (convolutionWuWindows N Δ V) j ∧
      ∀ x ∈ L.labels, PhysicalGeometry N (wuLocalExponent k δ/10) L x ∧
        Sifted (x.1*x.2.2.2.1*x.2.2.1*N) x.2.2.2.2 x.2.1 ∧
        ∀ r, r.Prime → r ∣ L.cofactor x → r.Coprime N →
          (N : ℝ)^(wuLocalExponent k δ/10) ≤ (r : ℝ) := by
  obtain ⟨T,hT,hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  have hW : ∀ a q, q ∈ convolutionWuWindows N Δ V a →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ/10) ≤ (q : ℝ) :=
    fun a q hq => ⟨(hw N hN i Δ V hb a q hq).1, (hw N hN i Δ V hb a q hq).2.2⟩
  refine ⟨(sourceFamily_dictionary N δ Δ V p j).1,
    (sourceFamily_dictionary N δ Δ V p j).2, ?_⟩
  intro x hx
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
    (mem_filter.mp hx).1
  exact ⟨actual_source_geometry (by omega) hδ hδhi hb p hp j hx,
    (sourceFamily_mask N δ Δ V p j hx).2,
    actual_source_relative (by omega) hδ hδhi hb p hp j hW hprof⟩

end Wu2008DoubleSieve.FourPrimeNonunit
