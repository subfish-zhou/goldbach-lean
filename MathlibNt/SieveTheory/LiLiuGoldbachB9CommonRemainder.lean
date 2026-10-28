import MathlibNt.SieveTheory.LiLiuGoldbachB9PanDistribution

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- Inclusion of the actual strict-level divisor support, still including d = 1. -/
theorem goldbachB9PlusBoundingSieve_levelSupport_subset
    (N : ℕ) (Z Δ : ℝ) (Q : ℕ) (hQ : Nat.floor Δ ≤ Q) :
    (goldbachB10ProdPrimes N Z).divisors.filter (fun d => d < Nat.floor Δ + 1) ⊆
      (Icc 1 Q).filter (fun d => d ∣ goldbachB10ProdPrimes N Z) := by
  intro d hd
  obtain ⟨hdiv, hlt⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdiv, by omega⟩,
    (Nat.mem_divisors.mp hdiv).1⟩


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig