import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitRelative
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughPurification

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical

/-- The only additional predicate is roughness of the original residual at p3. -/
def profileRough (x : Gamma16Profile) : Prop :=
  LiLiuPrereqBuchstab.Rough (x.2.1 : ℝ) x.2.2.2.2

noncomputable def roughFamily {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    LabelledPhysical.Family Gamma16Profile N :=
  (sourceFamily N δ Δ V p j).restrictLabels profileRough

theorem mem_roughFamily_labels {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (j : Fin 4) (x : Gamma16Profile) :
    x ∈ (roughFamily N δ Δ V p j).labels ↔
      x ∈ (sourceFamily N δ Δ V p j).labels ∧ profileRough x := mem_filter

/-- All numerical data and the literal last-prime interval are unchanged. -/
theorem roughFamily_data {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    (roughFamily N δ Δ V p j).weight = (sourceFamily N δ Δ V p j).weight ∧
    (roughFamily N δ Δ V p j).cofactor = (sourceFamily N δ Δ V p j).cofactor ∧
    (roughFamily N δ Δ V p j).lower = (sourceFamily N δ Δ V p j).lower ∧
    (roughFamily N δ Δ V p j).upper = (sourceFamily N δ Δ V p j).upper ∧
    (roughFamily N δ Δ V p j).primes = (sourceFamily N δ Δ V p j).primes :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem roughFamily_original_profile {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (j : Fin 4) {x : Gamma16Profile}
    (hx : x ∈ (roughFamily N δ Δ V p j).labels) :
    x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j ∧
      profileRough x ∧ 2 ≤ x.2.2.2.2 ∧
      Sifted (x.1*x.2.2.2.1*x.2.2.1*N) x.2.2.2.2 x.2.1 := by
  have hs := (mem_roughFamily_labels p j x).mp hx
  exact ⟨(mem_filter.mp hs.1).1,hs.2,sourceFamily_mask N δ Δ V p j hs.1⟩

/-- Reuse the original arbitrary-test dictionary, including deleted empty fibres. -/
theorem roughFamily_test_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) (test : Gamma16Profile → ℕ → ℝ) :
    (∑ x ∈ (roughFamily N δ Δ V p j).labels,
      ∑ q ∈ (roughFamily N δ Δ V p j).primes x, test x q) =
      ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter profileRough,
        ∑ q ∈ actualRawFibre N δ p j x, test x q := by
  have h := sourceFamily_test_dictionary N δ Δ V p j
    (fun x q => if profileRough x then test x q else 0)
  simpa only [roughFamily, LabelledPhysical.Family.restrictLabels,
    LabelledPhysical.Family.primes, sum_filter, sum_ite_irrel, sum_const_zero] using h

theorem roughFamily_mass_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    (roughFamily N δ Δ V p j).mass =
      ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter profileRough,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          (actualRawFibre N δ p j x).card := by
  simpa only [LabelledPhysical.Family.mass, roughFamily,
    LabelledPhysical.Family.restrictLabels, sourceFamily, actualFamily, physicalFamily,
    sum_const, nsmul_eq_mul, mul_comm] using
    roughFamily_test_dictionary N δ Δ V p j
      (fun x _ => (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ))

theorem roughFamily_primeMass_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    (roughFamily N δ Δ V p j).primeMass =
      ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter profileRough,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          (actualFibre N δ p j x).card := by
  have h := roughFamily_test_dictionary N δ Δ V p j
    (fun x q => if (N-gamma16Cofactor x*q).Prime then
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) else 0)
  simp only [← sum_filter, sum_const, nsmul_eq_mul] at h
  simpa only [LabelledPhysical.Family.primeMass, roughFamily,
    LabelledPhysical.Family.restrictLabels, sourceFamily, actualFamily, physicalFamily,
    actualRawFibre, actualFibre, fibre_eq_raw_filter, mul_comm] using h

/-- This is solely a proof adapter, never a replacement of the four-prime family. -/
def squareProfile (x : Gamma16Profile) : HighNonunit.Profile :=
  ⟨x.1,[x.2.2.2.1,x.2.2.1],x.2.1,x.2.2.2.2⟩

theorem squareProfile_cofactor (x : Gamma16Profile) :
    HighNonunit.cofactor (squareProfile x) = gamma16Cofactor x := by
  simp only [squareProfile, HighNonunit.cofactor, gamma16Cofactor,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem squareProfile_mask (N : ℕ) (x : Gamma16Profile) :
    (squareProfile x).1 * (squareProfile x).2.1.prod * N =
      x.1*x.2.2.2.1*x.2.2.1*N := by
  simp only [squareProfile, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem squareProfile_rough (x : Gamma16Profile) :
    HighNonunit.profileRough (squareProfile x) ↔ profileRough x := Iff.rfl

/-- Good masked nonrough labels force a square in the original cofactor E. -/
theorem masked_good_nonrough_square {N : ℕ} {Y : ℝ} {x : Gamma16Profile}
    (hs : Sifted (x.1*x.2.2.2.1*x.2.2.1*N) x.2.2.2.2 x.2.1)
    (hc : (gamma16Cofactor x).Coprime N) (hn : ¬ profileRough x)
    (hrel : ∀ r, r.Prime → r ∣ gamma16Cofactor x → r.Coprime N → Y ≤ (r : ℝ)) :
    LabelledPhysical.Sq (gamma16Cofactor x) Y := by
  have hs' : Sifted ((squareProfile x).1*(squareProfile x).2.1.prod*N)
      (squareProfile x).2.2.2 (squareProfile x).2.2.1 := by
    rw [squareProfile_mask]
    exact hs
  have h := HighNonunit.masked_good_nonrough_square hs'
    (by simpa only [squareProfile_cofactor] using hc)
    (fun h => hn ((squareProfile_rough x).mp h))
    (by simpa only [squareProfile_cofactor] using hrel)
  simpa only [squareProfile_cofactor] using h

/-- Uniform prime-layer purification; no exceptional term has been paid. -/
theorem source_primeMass_rough_square_bad (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).primeMass +
        (sourceFamily N δ Δ V p j).squareRawMass ((N : ℝ)^(wuLocalExponent k δ/10)) +
        (sourceFamily N δ Δ V p j).noncoprimePart.primeMass := by
  obtain ⟨T,hT,hu⟩ := actual_family_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  apply LabelledPhysical.Family.primeMass_le_restrict_add_square_add_bad
  intro x hx hc hn
  have hi := (hu N hN i Δ V hb p hp j).2.2 x hx
  exact masked_good_nonrough_square hi.2.1 hc hn hi.2.2

/-- Summation over the original four words retains raw-square and prime-bad-N types. -/
theorem source_prime_four_le_rough_square_bad (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 4, (roughFamily N δ Δ V p j).primeMass) +
        (∑ j : Fin 4, (sourceFamily N δ Δ V p j).squareRawMass
          ((N : ℝ)^(wuLocalExponent k δ/10))) +
        ∑ j : Fin 4, (sourceFamily N δ Δ V p j).noncoprimePart.primeMass := by
  obtain ⟨T,hT,hu⟩ := source_primeMass_rough_square_bad k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  simpa only [sum_add_distrib] using
    sum_le_sum (s := (univ : Finset (Fin 4))) (fun j _ => hu N hN i Δ V hb p hp j)

end Wu2008DoubleSieve.FourPrimeNonunit
