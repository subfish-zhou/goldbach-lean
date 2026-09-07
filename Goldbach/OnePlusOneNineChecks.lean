import Goldbach.OnePlusOneNine

/-! # Independent literal and axiom checks for the Li–Liu public interface -/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Goldbach.OnePlusOneNineChecks

/-- Independent literal Li–Liu specification with exact natural powers. -/
theorem oneNine :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ r ^ 10 ≤ q ^ 9 :=
  Goldbach.one_plus_one_nine

/-- Extensional equality avoids relying on definitional equality of filter deciders. -/
theorem count_is_literal (N : ℕ) :
    (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19 N : ℝ) =
      (((Finset.range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ ∃ r q : ℕ, (r = 1 ∨ r.Prime) ∧ q.Prime ∧
          N = p + r * q ∧ r ^ 10 ≤ q ^ 9)).card : ℝ) := by
  have hs : MathlibNt.SieveTheory.LiLiuOnePlusOneNine.onePlusOneNineRepresentedPrimes N =
      (Finset.range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ ∃ r q : ℕ, (r = 1 ∨ r.Prime) ∧ q.Prime ∧
          N = p + r * q ∧ r ^ 10 ≤ q ^ 9) := by
    ext p
    simp only [MathlibNt.SieveTheory.LiLiuOnePlusOneNine.mem_onePlusOneNineRepresentedPrimes_iff,
      Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
      MathlibNt.SieveTheory.LiLiuOnePlusOneNine.IsOnePlusOneNineRepresentation]
  exact congrArg (fun s : Finset ℕ => (s.card : ℝ)) hs

/-- Literal count of distinct primes p, rather than of representation witnesses. -/
theorem paperCount :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (0.0004 : ℝ) *
        (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ 2) <
        (((Finset.range (N + 1)).filter (fun p : ℕ =>
          p.Prime ∧ ∃ r q : ℕ, (r = 1 ∨ r.Prime) ∧ q.Prime ∧
            N = p + r * q ∧ r ^ 10 ≤ q ^ 9)).card : ℝ) := by
  have hcoeff : (0.0004 : ℝ) = 1 / 2500 := by norm_num
  obtain ⟨K,hK,h⟩ :=
    Goldbach.one_plus_one_nine_count
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hb := h N hN hEven
  rw [count_is_literal N] at hb
  simpa only [hcoeff] using hb

end Goldbach.OnePlusOneNineChecks

#check @Goldbach.one_plus_one_nine
#print axioms Goldbach.one_plus_one_nine
#check @Goldbach.one_plus_one_nine_real
#print axioms Goldbach.one_plus_one_nine_real
#check @Goldbach.one_plus_one_nine_count
#print axioms Goldbach.one_plus_one_nine_count
#check @Goldbach.one_plus_one_nine_lower_bound
#print axioms Goldbach.one_plus_one_nine_lower_bound
