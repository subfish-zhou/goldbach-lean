import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledCoprimeOutputSplit

/-! Finite sieve consumption with the exceptional term retained explicitly.
No R1, R2, small-output, or actual-high-family Theta payment is claimed. -/
namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Finset
open scoped Classical
open MathlibNt.SieveTheory.SwitchingPrinciple

variable {α : Type*} {N : ℕ} (L : Wu2008DoubleSieve.LabelledPhysical.Family α N)

/-- The original family is bounded by the good sieve and the literal bad output sum. -/
theorem prime_upper_coprime_finite_sum (hN : 0 < N) (he : Even N)
    (D : ℕ) (Z : ℝ) (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    L.primeMass ≤ L.coprimePart.mass * ordinaryRosserMainSum true N 1 D Z +
      L.coprimePart.R1 D Z + L.coprimePart.R2 D Z + L.coprimePart.small Z +
      ∑ b ∈ N.primeFactors, L.weightAt b := by
  rw [L.primeMass_coprime_split]
  exact add_le_add (L.coprimePart.prime_upper_finite he D Z hD hZ)
    (L.noncoprimePart_primeMass_le_sum hN)

/-- Local original-weight bounds yield an explicit exceptional logarithmic term. -/
theorem prime_upper_coprime_finite_log (hN : 0 < N) (he : Even N)
    (D : ℕ) (Z : ℝ) (hD : 1 < D) (hZ : Z ≤ (D : ℝ))
    {F : ℝ} (hF : 0 ≤ F) (hlocal : ∀ b ∈ N.primeFactors, L.weightAt b ≤ F) :
    L.primeMass ≤ L.coprimePart.mass * ordinaryRosserMainSum true N 1 D Z +
      L.coprimePart.R1 D Z + L.coprimePart.R2 D Z + L.coprimePart.small Z +
      F * Real.log N / Real.log 2 := by
  rw [L.primeMass_coprime_split]
  exact add_le_add (L.coprimePart.prime_upper_finite he D Z hD hZ)
    (L.noncoprimePart_primeMass_le_log hN hF hlocal)

end Wu2008DoubleSieve.LabelledPhysical.Family
