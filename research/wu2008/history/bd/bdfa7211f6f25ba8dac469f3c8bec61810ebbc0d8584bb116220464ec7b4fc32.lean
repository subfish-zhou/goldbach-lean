import MathlibNt.Wu2008DoubleSieve.NinthProductProfileGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3R1Distribution

/-!
# The ninth product profile in the existing balanced AP consumer

This specializes the existing distribution theorem to the output-independent
pair-product support and unit coefficient. The cofactor sum stays inside
the absolute value, with its coprimality mask and actual prime-count center.
It is not an upper sieve for T9 or an estimate of the F9 integral.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem T9_card_eq_ninth_product_profiles (N : ℕ) :
    (T9 N (ninthProfileW N) (ninthProfileU N)).card =
      ∑ m ∈ ninthProductSupport N,
        ((omega3ProfilePrimes N (ninthProfileLower (ninthProfileU N))
          (ninthProfileUpper N m)).filter (fun c => (N - m * c).Prime)).card :=
  T9_card_eq_product_profiles N (ninthProfileW N) (ninthProfileU N)

/-- The profile center is its actual prime count divided by phi, not li. -/
theorem ninth_product_profile_error_eq (N q m : ℕ) :
    omega3ProfileError N q m (ninthProfileLower (ninthProfileU N))
      (ninthProfileUpper N m) =
      (((omega3ProfilePrimes N (ninthProfileLower (ninthProfileU N))
        (ninthProfileUpper N m)).filter
          (fun c => Nat.ModEq q (m * c) N)).card : ℝ) -
        (omega3ProfilePrimes N (ninthProfileLower (ninthProfileU N))
          (ninthProfileUpper N m)).card / (Nat.totient q : ℝ) := rfl

/-- The prime-count-centered reduced-residue AP branch, with one threshold
uniform in N and Z. All support/profile hypotheses are proved, not assumed. -/
theorem ninth_product_profile_balanced_distribution (A : ℝ) {δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ Z : ℝ,
      (∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
        (3 : ℝ) ^ q.primeFactors.card *
          |∑ m ∈ (ninthProductSupport N).filter (fun m => m.Coprime q),
            omega3ProfileError N q m (ninthProfileLower (ninthProfileU N))
              (ninthProfileUpper N m)|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨C, hC, T, _, hT⟩ :=
    omega3_balanced_interval_distribution A ninthProfileK2 1 hA
      (by norm_num [ninthProfileK2]) (by norm_num) hδ
  refine ⟨C, hC, max T 512, le_max_right _ _, ?_⟩
  intro N hN Z
  have hNT : T ≤ N := (le_max_left _ _).trans hN
  have hN512 : 512 ≤ N := (le_max_right _ _).trans hN
  have h := hT N hNT (ninthProductSupport N) (fun _ => 1)
    (fun _ => ninthProfileLower (ninthProfileU N)) (ninthProfileUpper N)
    (fun m hm => ⟨(ninthProductSupport_geometry hN512 m hm).1,
      (ninthProductSupport_geometry hN512 m hm).2.1⟩)
    (by intro m _; norm_num)
    (fun m hm => (ninthProductSupport_geometry hN512 m hm).2.2) Z
  simpa only [one_mul] using h

end Wu2008DoubleSieve
