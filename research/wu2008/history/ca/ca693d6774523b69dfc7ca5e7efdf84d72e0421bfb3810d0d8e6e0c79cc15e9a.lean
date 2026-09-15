import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
# Wu's singular-series normalization

Wu (2008), (1.2), printed pages 367--368; the frozen 1+1.8938 manuscript,
Section 1. The universal product is indexed by actual odd primes, and the
finite product by odd prime divisors. This is `C(N)`, not `2 C(N)`.
-/

namespace Wu2008DoubleSieve

open Finset
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical

def OddPrimes : Set ℕ := {p | p.Prime ∧ 2 < p}

private theorem oddPrime_indicator (p : ℕ) :
    OddPrimes.mulIndicator (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1) ^ 2) p =
      1 + liuBaseDeviation p := by
  by_cases hp : p ∈ OddPrimes
  · rw [Set.mulIndicator_of_mem hp]
    exact (one_add_liuBaseDeviation_eq_baseFactor hp.1 hp.2).symm
  · rw [Set.mulIndicator_of_notMem hp]
    change ¬(p.Prime ∧ 2 < p) at hp
    simp [liuBaseDeviation, hp]

theorem multipliable_wu_universal_product :
    Multipliable (fun p : OddPrimes => 1 - 1 / ((p.val : ℝ) - 1) ^ 2) := by
  apply (multipliable_subtype_iff_mulIndicator
    (f := fun q : ℕ => (1 : ℝ) - 1 / ((q : ℝ) - 1) ^ 2) (s := OddPrimes)).mpr
  convert multipliable_one_add_liuBaseDeviation using 1
  exact funext oddPrime_indicator

theorem wu_universal_product_eq_liu :
    (∏' p : OddPrimes, (1 - 1 / ((p.val : ℝ) - 1) ^ 2)) = liuUniversalProduct := by
  calc
    _ = ∏' p : ℕ, OddPrimes.mulIndicator
        (fun q : ℕ => (1 : ℝ) - 1 / ((q : ℝ) - 1) ^ 2) p :=
      _root_.tprod_subtype OddPrimes (fun q : ℕ => (1 : ℝ) - 1 / ((q : ℝ) - 1) ^ 2)
    _ = _ := tprod_congr oddPrime_indicator

theorem oddPrimeDivisors_eq (N : ℕ) (hN : 0 < N) :
    (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N) =
      N.primeFactors.filter (fun p => 2 < p) := by
  ext p
  simp only [mem_filter, mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨_, hp, hp2, hpdvd⟩
    exact ⟨⟨hp, hpdvd, hN.ne'⟩, hp2⟩
  · rintro ⟨⟨hp, hpdvd, _⟩, hp2⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hN hpdvd), hp, hp2, hpdvd⟩

/-- The literal two-product expression for Wu's `C(N)`, used for `N > 0`. -/
noncomputable def wuSingularSeries (N : ℕ) : ℝ :=
  (∏' p : OddPrimes, (1 - 1 / ((p.val : ℝ) - 1) ^ 2)) *
    ∏ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N),
      ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem wuSingularSeries_eq_liu (N : ℕ) (hN : 0 < N) :
    wuSingularSeries N = liuSingularSeries N := by
  rw [wuSingularSeries, wu_universal_product_eq_liu, oddPrimeDivisors_eq N hN]
  exact mul_comm _ _

theorem wuSingularSeries_pos (N : ℕ) (hN : 0 < N) :
    0 < wuSingularSeries N := by
  rw [wuSingularSeries_eq_liu N hN]
  exact liuSingularSeries_pos N

end Wu2008DoubleSieve
