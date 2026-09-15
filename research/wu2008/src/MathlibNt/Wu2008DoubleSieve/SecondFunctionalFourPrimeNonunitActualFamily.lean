import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitPhysical

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical
open FourPrimeUnit (word)

/-- The four original words and all prefix colour thresholds are unchanged. -/
noncomputable def actualFamily {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    LabelledPhysical.Family Gamma16Profile N :=
  physicalFamily N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j) hd

noncomputable def actualRawFibre (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (j : Fin 4) : Gamma16Profile → Finset ℕ :=
  rawFibre N (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualRawMass {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : ℝ :=
  ∑ x ∈ actualProfiles N δ p W j,
    (convolutionCoeff W x.1 : ℝ) * (actualRawFibre N δ p j x).card

theorem actualFamily_labels {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (actualFamily N δ p W j hd).labels = (actualProfiles N δ p W j).filter
      (fun x => physicalLower (fun d => wuLocalCutoff N δ d p.kappa2)
        (fun d => wuLocalCutoff N δ d p.kappa3) (word j) x ≤
        physicalUpper N (fun d => wuLocalCutoff N δ d p.kappa3)
          (fun d => wuLocalCutoff N δ d p.s) (word j) x) := rfl

theorem actualFamily_dictionary {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (actualFamily N δ p W j hd).primeMass = actualEnvelope N δ p W j ∧
    (actualFamily N δ p W j hd).mass = actualRawMass N δ p W j :=
  ⟨physical_primeMass_dictionary hd, physical_mass_dictionary hd⟩

theorem actualFamily_data {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (x : Gamma16Profile) :
    (actualFamily N δ p W j hd).weight x = (convolutionCoeff W x.1 : ℝ) ∧
    (actualFamily N δ p W j hd).cofactor x =
      x.1*x.2.2.2.2*x.2.2.2.1*x.2.2.1*x.2.1 := ⟨rfl,rfl⟩

theorem actualFamily_fibres {i N : ℕ} {δ : ℝ} (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    {x : Gamma16Profile} (hx : x ∈ actualProfiles N δ p W j) :
    (actualFamily N δ p W j hd).primes x = actualRawFibre N δ p j x ∧
    ((actualFamily N δ p W j hd).primes x).filter
      (fun q => (N-gamma16Cofactor x*q).Prime) = actualFibre N δ p j x := by
  have hraw : (actualFamily N δ p W j hd).primes x = actualRawFibre N δ p j x :=
    (rawFibre_eq_profile (N := N) _ _ _ _ x (profile_cofactor_pos hd hx)).symm
  refine ⟨hraw, ?_⟩
  rw [hraw]
  exact (fibre_eq_raw_filter N _ _ _ _ x).symm

theorem actualFamily_test_dictionary {i N : ℕ} {δ : ℝ} (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (test : Gamma16Profile → ℕ → ℝ) :
    (∑ x ∈ (actualFamily N δ p W j hd).labels,
      ∑ q ∈ (actualFamily N δ p W j hd).primes x, test x q) =
    ∑ x ∈ actualProfiles N δ p W j, ∑ q ∈ actualRawFibre N δ p j x, test x q :=
  physical_sum_dictionary hd test

/-- Positivity of the convolution support is provided inside this construction. -/
noncomputable def sourceFamily {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    LabelledPhysical.Family Gamma16Profile N :=
  actualFamily N δ p (convolutionWuWindows N Δ V) j
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd)

structure PhysicalGeometry (N : ℕ) (η : ℝ) (L : LabelledPhysical.Family Gamma16Profile N)
    (x : Gamma16Profile) : Prop where
  positive : 0 < L.cofactor x
  le_N : L.cofactor x ≤ N
  power_lower : (N : ℝ)^η ≤ L.cofactor x
  power_upper : (L.cofactor x : ℝ) ≤ (N : ℝ)^(1-η)
  lower_two : 2 ≤ L.lower x
  lower_large : (N : ℝ)^η ≤ L.lower x
  feasible : L.lower x ≤ L.upper x
  physical : (L.cofactor x : ℝ) * L.upper x ≤ N

/-- Every retained label has power-gap geometry, including empty prime-output fibres. -/
theorem actual_source_geometry {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 4) {x : Gamma16Profile}
    (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    PhysicalGeometry N (wuLocalExponent k δ / 10) (sourceFamily N δ Δ V p j) x := by
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
    (mem_filter.mp hx).1
  obtain ⟨hd,hm,_,_,_,_,_,_,_,_,hcap⟩ := profile_data hprof
  have hlarge := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd hm
  have hg := (sourceFamily N δ Δ V p j).geometry x hx
  have hpos : 0 < gamma16Cofactor x := hg.1
  have hle : gamma16Cofactor x ≤ N :=
    (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ)^(wuLocalExponent k δ / 10) ≤ gamma16Cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos,hle,hpow,omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1,hlarge.2.trans (le_max_left _ _),hg.2.2.1,hg.2.2.2⟩

theorem sourceFamily_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    (sourceFamily N δ Δ V p j).primeMass =
      actualEnvelope N δ p (convolutionWuWindows N Δ V) j ∧
    (sourceFamily N δ Δ V p j).mass =
      actualRawMass N δ p (convolutionWuWindows N Δ V) j :=
  actualFamily_dictionary N δ p (convolutionWuWindows N Δ V) j _

theorem sourceFamily_test_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) (test : Gamma16Profile → ℕ → ℝ) :
    (∑ x ∈ (sourceFamily N δ Δ V p j).labels,
      ∑ q ∈ (sourceFamily N δ Δ V p j).primes x, test x q) =
    ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j,
      ∑ q ∈ actualRawFibre N δ p j x, test x q :=
  actualFamily_test_dictionary p (convolutionWuWindows N Δ V) j _ test

/-- The original nonunit and masked-sifting conditions hold on all source labels. -/
theorem sourceFamily_mask {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) {x : Gamma16Profile}
    (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    2 ≤ x.2.2.2.2 ∧ Sifted (x.1*x.2.2.2.1*x.2.2.1*N) x.2.2.2.2 x.2.1 := by
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
    (mem_filter.mp hx).1
  obtain ⟨_,_,_,_,_,hn,hs,_⟩ := profile_data hprof
  exact ⟨hn,hs⟩

end Wu2008DoubleSieve.FourPrimeNonunit
