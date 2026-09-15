import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePower
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTwoPower
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobalBridge

/-!
# Unconditional complete Weil and Fouvry interval estimates

The odd-prime-power Gauss argument and the separate two-power stationary bound
supply every primitive local estimate. Exact frequency descent and twisted CRT
then give the divisor/gcd envelope for every positive modulus. The existing
Fourier completion yields Fouvry's Lemma 3, uniformly in signed frequencies and
real interval endpoints; no complete-sum estimate remains as a hypothesis.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_prime_power_primitive_weil (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ) := by
  by_cases hp : p = 2
  · subst p
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      completeKloosterman_two_power_primitive_weil k a d hprimitive
  · exact completeKloosterman_odd_prime_power_primitive_weil p k hp a d hprimitive

/-- The full complete-sum bound, including modulus one, nonprimitive frequency
pairs, and zero or negative frequencies. -/
theorem completeKloosterman_weil (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) *
        Real.sqrt q := by
  exact completeKloosterman_weil_of_primitive_prime_power
    (fun p k _ a d ↦ completeKloosterman_prime_power_primitive_weil p k a d) q a d

theorem completeKloosterman_weil_zmod (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) :
    ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (m.val.gcd d.natAbs)) *
        Real.sqrt q := by
  exact completeKloosterman_weil_zmod_of_primitive_prime_power
    (fun p k _ a d ↦ completeKloosterman_prime_power_primitive_weil p k a d) q m d

/-- F87 Lemma 3 for the actual reciprocal sum over `X < c ≤ Y`, with a single
constant for all positive moduli, signed frequencies, and intervals of length
at most the modulus. -/
theorem reciprocalInterval_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (X Y : ℝ),
      X ≤ Y → Y - X ≤ q →
      ‖reciprocalInterval q d X Y‖ ≤
        C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  exact reciprocalInterval_weil_to_fouvry
    (fun q _ m d ↦ completeKloosterman_weil_zmod q m d) hε

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
