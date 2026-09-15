import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitPhysical

namespace Wu2008DoubleSieve.HighNonunit
open Finset
open scoped Classical

/-- The literal actual profile family: only geometric deletion, unchanged coefficients. -/
noncomputable def actualFamily {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) : LabelledPhysical.Family Profile N :=
  physicalFamily N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word high) hd

noncomputable def actualRawFibre (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters) :
    Profile → Finset ℕ :=
  rawFibre N (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)

noncomputable def actualRawMass {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) : ℝ :=
  ∑ x ∈ actualProfiles N δ p W high,
    (convolutionCoeff W x.1 : ℝ) * (actualRawFibre N δ p x).card

theorem actualFamily_labels {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (actualFamily N δ p W high hd).labels = (actualProfiles N δ p W high).filter
      (fun x => physicalLower (fun d => wuLocalCutoff N δ d p.kappa3) x ≤
        physicalUpper N (fun d => wuLocalCutoff N δ d p.s) x) := rfl

theorem actualFamily_dictionary {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (actualFamily N δ p W high hd).primeMass = actualEnvelope N δ p W high ∧
    (actualFamily N δ p W high hd).mass = actualRawMass N δ p W high :=
  ⟨physical_primeMass_dictionary hd, physical_mass_dictionary hd⟩

theorem actualFamily_data {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (x : Profile) :
    (actualFamily N δ p W high hd).weight x = (convolutionCoeff W x.1 : ℝ) ∧
    (actualFamily N δ p W high hd).cofactor x =
      x.1*x.2.2.2*(x.2.1 ++ [x.2.2.1]).prod := ⟨rfl, rfl⟩

theorem actualFamily_fibres {i N : ℕ} {δ : ℝ} (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    {x : Profile} (hx : x ∈ actualProfiles N δ p W high) :
    (actualFamily N δ p W high hd).primes x = actualRawFibre N δ p x ∧
    ((actualFamily N δ p W high hd).primes x).filter
      (fun q => (N-cofactor x*q).Prime) = actualFibre N δ p x := by
  have hraw : (actualFamily N δ p W high hd).primes x = actualRawFibre N δ p x := by
    exact (rawFibre_eq_profile (N := N)
      (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)
      x (profile_cofactor_pos hd hx)).symm
  refine ⟨hraw, ?_⟩
  rw [hraw]
  exact (fibre_eq_raw_filter N (fun d => wuLocalCutoff N δ d p.kappa3)
    (fun d => wuLocalCutoff N δ d p.s) x).symm

theorem actualFamily_test_dictionary {i N : ℕ} {δ : ℝ} (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (test : Profile → ℕ → ℝ) :
    (∑ x ∈ (actualFamily N δ p W high hd).labels,
      ∑ q ∈ (actualFamily N δ p W high hd).primes x, test x q) =
    ∑ x ∈ actualProfiles N δ p W high, ∑ q ∈ actualRawFibre N δ p x, test x q :=
  physical_sum_dictionary hd test

/-- Source-window positivity is supplied internally; no geometry or roughness proof argument. -/
noncomputable def sourceFamily {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : LabelledPhysical.Family Profile N :=
  actualFamily N δ p (convolutionWuWindows N Δ V) high
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd)

/-- All bounds concern every retained profile, not only nonempty output fibres. -/
structure PhysicalGeometry (N : ℕ) (η : ℝ) (L : LabelledPhysical.Family Profile N)
    (x : Profile) : Prop where
  positive : 0 < L.cofactor x
  le_N : L.cofactor x ≤ N
  power_lower : (N : ℝ)^η ≤ L.cofactor x
  power_upper : (L.cofactor x : ℝ) ≤ (N : ℝ)^(1-η)
  lower_two : 2 ≤ L.lower x
  lower_large : (N : ℝ)^η ≤ L.lower x
  feasible : L.lower x ≤ L.upper x
  physical : (L.cofactor x : ℝ) * L.upper x ≤ N

theorem actual_source_geometry {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (high : Bool) {x : Profile}
    (hx : x ∈ (sourceFamily N δ Δ V p high).labels) :
    PhysicalGeometry N (wuLocalExponent k δ / 10) (sourceFamily N δ Δ V p high) x := by
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high :=
    (mem_filter.mp hx).1
  obtain ⟨hd, _, hm, _, _, hcap⟩ := profile_data hprof
  have hlarge := mother_window_lower hN hδ hδhi hb p hp hd hm
  have hg := (sourceFamily N δ Δ V p high).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hle : cofactor x ≤ N := (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ)^(wuLocalExponent k δ / 10) ≤ cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos, hle, hpow, omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1, hlarge.2.trans (le_max_left _ _), hg.2.2.1, hg.2.2.2⟩

/-- Relative roughness of the complete cofactor, with the extra penultimate really multiplied back. -/
theorem actual_source_relative {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (high : Bool)
    (hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ))
    {x : Profile} (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high) :
    ∀ q, q.Prime → q ∣ cofactor x → q.Coprime N →
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
  obtain ⟨hd, hpre, hm, _, hs, _⟩ := profile_data hx
  have hpen := mother_window_lower hN hδ hδhi hb p hp hd hm
  have hprefix := RelativeRoughness.masked_prefix x.2.1 hs hpen.2
    (fun q hq hqd => omega3_support_prime_lower _ hW hd hq hqd)
    (fun r hr => mother_window_lower hN hδ hδhi hb p hp hd (hpre r hr))
  have hlast : ∀ q : ℕ, q.Prime → q ∣ x.2.2.1 → q.Coprime N →
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
    intro q hq hqd _
    have heq : q = x.2.2.1 := ((Nat.dvd_prime hpen.1).mp hqd).resolve_left hq.ne_one
    simpa only [heq] using hpen.2
  have hfull := RelativeRoughness.mul hprefix hlast
  simpa only [cofactor, List.prod_append, List.prod_singleton, mul_assoc, mul_left_comm,
    mul_comm] using hfull

/-- A single threshold precedes N, all boxes and all mother parameters and both high words. -/
theorem actual_family_uniform (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      (∀ j q, q ∈ convolutionWuWindows N Δ V j →
        q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) ∧
      ∀ (p : SecondFunctionalParameters), p.MotherAdmissible → ∀ high : Bool,
        let L := sourceFamily N δ Δ V p high
        L.primeMass = actualEnvelope N δ p (convolutionWuWindows N Δ V) high ∧
        L.mass = actualRawMass N δ p (convolutionWuWindows N Δ V) high ∧
        ∀ x ∈ L.labels, PhysicalGeometry N (wuLocalExponent k δ / 10) L x ∧
          Sifted (x.1*x.2.1.prod*N) x.2.2.2 x.2.2.1 ∧
          ∀ q, q.Prime → q ∣ L.cofactor x → q.Coprime N →
            (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
  obtain ⟨T, hT, hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb
  have hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) :=
    fun j q hq => ⟨(hw N hN i Δ V hb j q hq).1, (hw N hN i Δ V hb j q hq).2.2⟩
  refine ⟨hW, ?_⟩
  intro p hp high
  have hdict := actualFamily_dictionary N δ p (convolutionWuWindows N Δ V) high
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd)
  refine ⟨hdict.1, hdict.2, ?_⟩
  intro x hx
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high :=
    (mem_filter.mp hx).1
  exact ⟨actual_source_geometry (by omega) hδ hδhi hb p hp high hx,
    (profile_data hprof).2.2.2.2.1,
    actual_source_relative (by omega) hδ hδhi hb p hp high hW hprof⟩

theorem mother_source_le_family (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (high : Bool) :
    actualSource N δ p (convolutionWuWindows N Δ V) high ≤
      (sourceFamily N δ Δ V p high).primeMass := by
  have hd := (actualFamily_dictionary N δ p (convolutionWuWindows N Δ V) high
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd)).1
  change actualSource N δ p (convolutionWuWindows N Δ V) high ≤
    (actualFamily N δ p (convolutionWuWindows N Δ V) high _).primeMass
  rw [hd]
  exact mother_source_le p hp hs hN he hδ hδhi hb high

end Wu2008DoubleSieve.HighNonunit
