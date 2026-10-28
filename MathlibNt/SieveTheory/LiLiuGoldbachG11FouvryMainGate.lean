import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryRectangle

open Finset Filter
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G11FiniteGate


end G11FiniteGate

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The existing twenty-factor bound extends to the actual short-prime product.
Repeated factors are allowed, and the short prime is counted at most once more. -/
theorem goldbachG11_effectiveProduct_mul_prime_factors {N m p : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) (hp : p.Prime)
    (hzp : (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) :
    0 < m*p ∧ (∀ q ∈ (m*p).primeFactors, (N : ℝ)^(4/53 : ℝ) ≤ (q : ℝ)) ∧
      (m*p).primeFactors.card ≤ 21 := by
  have hm0 := (goldbachG11ProductSupport_data (mem_filter.mp hm).1).1
  obtain ⟨hf, _heq, hk⟩ := goldbachG11EffectiveProductSupport_primeFactors hm
  refine ⟨Nat.mul_pos hm0 hp.pos, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    rcases hqp.dvd_mul.mp hqd with hqm | hqp'
    · exact hf q (Nat.mem_primeFactors.mpr ⟨hqp, hqm, hm0.ne'⟩)
    · rcases (Nat.dvd_prime hp).mp hqp' with hq1 | hqpEq
      · exact False.elim (hqp.ne_one hq1)
      · simpa only [hqpEq] using hzp
  · rw [Nat.primeFactors_mul hm0.ne' hp.ne_zero]
    have hcard := card_union_le m.primeFactors p.primeFactors
    have hpcard : p.primeFactors.card = 1 := by simp [hp]
    omega


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig