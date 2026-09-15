import MathlibNt.Wu2008DoubleSieve.NinthProductProfileDistribution
import MathlibNt.Wu2008DoubleSieve.Omega3SieveUpper

/-!
# The physical ninth-term weighted output sequence

The support is the full pair-product support, and every varying prime
label contributes once to its output weight. No output-prime condition
enters the mass or the coefficient sequence.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable def P9 (N m : ℕ) : Finset ℕ :=
  omega3ProfilePrimes N (ninthProfileLower (ninthProfileU N)) (ninthProfileUpper N m)

noncomputable def X9 (N : ℕ) : ℝ :=
  ∑ m ∈ ninthProductSupport N, ((P9 N m).card : ℝ)

noncomputable def B9 (N b : ℕ) : ℝ :=
  ∑ m ∈ ninthProductSupport N,
    (((P9 N m).filter (fun c => N - m * c = b)).card : ℝ)

noncomputable def ninthSieveDivisibleCount (N q : ℕ) : ℝ :=
  ∑ m ∈ ninthProductSupport N,
    (((P9 N m).filter (fun c => q ∣ N - m * c)).card : ℝ)

noncomputable def ninthSieveAPResidual (N q : ℕ) : ℝ :=
  ∑ m ∈ (ninthProductSupport N).filter (fun m => m.Coprime q),
    omega3ProfileError N q m (ninthProfileLower (ninthProfileU N)) (ninthProfileUpper N m)

noncomputable def ninthSieveMissingMass (N q : ℕ) : ℝ :=
  ∑ m ∈ (ninthProductSupport N).filter (fun m => ¬m.Coprime q),
    ((P9 N m).card : ℝ)

noncomputable def ninthSieveR1 (N D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    (3 : ℝ) ^ q.primeFactors.card * |ninthSieveAPResidual N q|

noncomputable def ninthSieveR2 (N D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) * ninthSieveMissingMass N q

noncomputable def ninthSiftedCount (N : ℕ) (Z : ℝ) : ℝ :=
  ∑ m ∈ ninthProductSupport N,
    (((P9 N m).filter (fun c => Sifted N (N - m * c) Z)).card : ℝ)

noncomputable def ninthBoundingSieve (N : ℕ) (he : Even N) (Z : ℝ) :
    BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := B9 N
  weights_nonneg := fun _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  totalMass := X9 N
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem X9_nonneg (N : ℕ) : 0 ≤ X9 N :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem ninthSieveMissingMass_nonneg (N q : ℕ) : 0 ≤ ninthSieveMissingMass N q :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem ninthProductSupport_pos {N m : ℕ} (hm : m ∈ ninthProductSupport N) :
    0 < m := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  exact ninthPair_product_pos ht

theorem P9_size {N m c : ℕ} (hm : m ∈ ninthProductSupport N) (hc : c ∈ P9 N m) :
    m * c < N := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  exact (ninthProfileUpper_nat_iff (ninthPair_N_pos ht) (ninthPair_product_pos ht)).mp
    (mem_filter.mp hc).2.2.2

theorem P9_prime {N m c : ℕ} (hc : c ∈ P9 N m) : c.Prime :=
  (mem_filter.mp hc).2.1

end Wu2008DoubleSieve
