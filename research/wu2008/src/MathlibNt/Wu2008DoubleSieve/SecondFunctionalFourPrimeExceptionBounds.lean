import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSieveSmall
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitRoughPurification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledSquareCofactor
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitExceptionPayment

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real Filter
open scoped Classical

/-- Exact original-sigma dictionary on prime outputs only. -/
theorem actualFamily_weightAt_prime {i N ell : ℕ} {δ : ℝ}
    (p : SecondFunctionalParameters) (W : Fin i → Finset ℕ) (j : Fin 4)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) (hell : ell.Prime) :
    (actualFamily N δ p W j hd).weightAt ell =
      ∑ x ∈ actualProfiles N δ p W j, (convolutionCoeff W x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card := by
  have ht := actualFamily_test_dictionary (N := N) (δ := δ) p W j hd
    (fun x q => if N-gamma16Cofactor x*q = ell then (convolutionCoeff W x.1 : ℝ) else 0)
  have hf (x : Gamma16Profile) (hx : x ∈ actualProfiles N δ p W j) :
      (actualRawFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell) =
        (actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell) := by
    rw [← (actualFamily_fibres p W j hd hx).2,
      (actualFamily_fibres p W j hd hx).1]
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨hq, he⟩
      exact ⟨⟨hq, he ▸ hell⟩, he⟩
    · rintro ⟨⟨hq, _⟩, he⟩
      exact ⟨hq, he⟩
  change (∑ x ∈ (actualFamily N δ p W j hd).labels,
    (convolutionCoeff W x.1 : ℝ) *
      (((actualFamily N δ p W j hd).primes x).filter
        (fun q => N-gamma16Cofactor x*q = ell)).card) = _
  simp only [← sum_filter, sum_const, nsmul_eq_mul] at ht
  simp only [show ∀ a b : ℝ, a*b=b*a from mul_comm] at ht
  rw [ht]
  exact sum_congr rfl (fun x hx => by rw [hf x hx])

/-- Source support supplies positivity internally; nonprime outputs are not identified. -/
theorem sourceFamily_weightAt_prime {i N ell : ℕ} {δ Δ : ℝ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) (hell : ell.Prime) :
    (sourceFamily N δ Δ V p j).weightAt ell =
      ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card :=
  actualFamily_weightAt_prime p _ j _ hell

/-- The genuine internal multiplicity theorem bounds every prime output, uniformly. -/
theorem source_prime_weightAt_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      ∀ ell : ℕ, ell.Prime →
        (sourceFamily N δ Δ V p j).weightAt ell ≤
          (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) := by
  obtain ⟨T,hT,hm⟩ := source_multiplicities k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j ell hell
  rw [sourceFamily_weightAt_prime V p j hell]
  exact (hm N hN i Δ V hb p hp j).2 ell

/-- Exceptional prime outputs are divisors of N; the full original weight is retained. -/
theorem source_bad_primeMass_log_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
        (sourceFamily N δ Δ V p j).noncoprimePart.primeMass ≤
          (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) * log N / log 2 := by
  obtain ⟨T,hT,hm⟩ := source_prime_weightAt_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  apply LabelledPhysical.Family.noncoprimePart_primeMass_le_log
    (sourceFamily N δ Δ V p j) (by have := hT.trans hN; omega) (by positivity)
  intro ell hell
  exact hm N hN i Δ V hb p hp j ell (Nat.prime_of_mem_primeFactors hell)


/-- Four original bad prime masses, with the unchanged internal G. -/
theorem source_bad_primeMass_four_log_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        (∑ j : Fin 4, (sourceFamily N δ Δ V p j).noncoprimePart.primeMass) ≤
          4 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) * log N / log 2 := by
  obtain ⟨T,hT,hm⟩ := source_bad_primeMass_log_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  calc
    _ ≤ ∑ _j : Fin 4, (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) *
        log N / log 2 := sum_le_sum (fun j _ => hm N hN i Δ V hb p hp j)
    _ = _ := by simp; ring

/-- The original weighted fixed-E bound pays raw squares; E geometry is in Family. -/
theorem source_squareRawMass_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      ∀ Y : ℝ, 2 ≤ Y →
        (sourceFamily N δ Δ V p j).squareRawMass Y ≤
          (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) * N * (1+log N)/(Y-1) := by
  obtain ⟨T,hT,hm⟩ := source_all_multiplicities k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j Y hY
  exact (sourceFamily N δ Δ V p j).squareRawMass_le hY (by positivity)
    ((hm N hN i Δ V hb p hp).1 j).2.2.1

end Wu2008DoubleSieve.FourPrimeNonunit
