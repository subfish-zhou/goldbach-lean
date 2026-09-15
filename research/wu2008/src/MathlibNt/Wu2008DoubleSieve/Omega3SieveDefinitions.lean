import MathlibNt.Wu2008DoubleSieve.Omega3ClosedEnlargement
import MathlibNt.Wu2008DoubleSieve.CanonicalUpperDensity

/-!
# The actual closed switched prime sequence and its two residuals

The cofactor labels retain every d,p2,p1,n representation, including empty
prime fibres. The convolution coefficient occurs once. The natural Rosser
level D is strict: all residual moduli satisfy q < D.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable def omega3SieveX {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ omega3CofactorLabels N δ s t W,
    (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ s c).card

noncomputable def omega3SieveAPCount (N : ℕ) (δ s : ℝ)
    (c : Omega3CofactorIndex) (q : ℕ) : ℕ :=
  ((omega3CofactorPrimeFibreLE N δ s c).filter
    (fun p => Nat.ModEq q (omega3CofactorValue c * p) N)).card

noncomputable def omega3SieveDivisibleCount {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (q : ℕ) : ℝ :=
  ∑ c ∈ omega3CofactorLabels N δ s t W,
    (convolutionCoeff W c.1 : ℝ) *
      (((omega3CofactorPrimeFibreLE N δ s c).filter
        (fun p => q ∣ N - omega3CofactorValue c * p)).card : ℝ)

noncomputable def omega3SieveAPResidual {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (q : ℕ) : ℝ :=
  ∑ c ∈ (omega3CofactorLabels N δ s t W).filter
      (fun c => (omega3CofactorValue c).Coprime q),
    (convolutionCoeff W c.1 : ℝ) *
      ((omega3SieveAPCount N δ s c q : ℝ) -
        (omega3CofactorPrimeFibreLE N δ s c).card / (Nat.totient q : ℝ))

noncomputable def omega3SieveMissingMass {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (q : ℕ) : ℝ :=
  ∑ c ∈ (omega3CofactorLabels N δ s t W).filter
      (fun c => ¬ (omega3CofactorValue c).Coprime q),
    (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ s c).card

noncomputable def omega3SieveModuli (N D : ℕ) (Z : ℝ) : Finset ℕ :=
  (ordinarySievePrimeProduct N Z).divisors.filter (fun q => q < D)

noncomputable def omega3SieveR1 {i : ℕ} (N D : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    (3 : ℝ) ^ q.primeFactors.card * |omega3SieveAPResidual N δ s t W q|

noncomputable def omega3SieveR2 {i : ℕ} (N D : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) *
      omega3SieveMissingMass N δ s t W q

noncomputable def omega3SieveOutputWeight {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (b : ℕ) : ℝ :=
  ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
    (((omega3CofactorPrimeFibreLE N δ s c).filter
      (fun p => N - omega3CofactorValue c * p = b)).card : ℝ)

/-- The source's w(q); BoundingSieve stores nu(q)=w(q)/q instead. -/
noncomputable def omega3SieveLocalWeight (N q : ℕ) : ℝ :=
  if Squarefree q ∧ q.Coprime N then (q : ℝ) / (Nat.totient q : ℝ) else 0

noncomputable def omega3GoldbachBoundingSieve {i : ℕ}
    (N : ℕ) (he : Even N) (δ s t Z : ℝ) (W : Fin i → Finset ℕ) :
    BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := omega3SieveOutputWeight N δ s t W
  weights_nonneg := fun _ => sum_nonneg fun _ _ => mul_nonneg
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  totalMass := omega3SieveX N δ s t W
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem omega3SieveX_nonneg {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : 0 ≤ omega3SieveX N δ s t W :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem omega3SieveMissingMass_nonneg {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (q : ℕ) : 0 ≤ omega3SieveMissingMass N δ s t W q :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem omega3SieveModuli_properties {N D q : ℕ} {Z : ℝ}
    (hq : q ∈ omega3SieveModuli N D Z) :
    0 < q ∧ Squarefree q ∧ q.Coprime N ∧ q < D := by
  obtain ⟨hq, hD⟩ := mem_filter.mp hq
  have hd := (Nat.mem_divisors.mp hq).1
  exact ⟨Nat.pos_of_mem_divisors hq,
    (ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hd,
    (ordinarySievePrimeProduct_coprime N Z).of_dvd_left hd, hD⟩

end Wu2008DoubleSieve
