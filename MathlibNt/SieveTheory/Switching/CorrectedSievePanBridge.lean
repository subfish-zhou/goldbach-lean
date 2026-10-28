import MathlibNt.SieveTheory.Switching.Weights

/-!
# The corrected sieve and the Pan counting bridge

Corrected candidate carriers, Selberg main terms, forbidden-prime products, and
Möbius/CRT identities connect finite arithmetic-progression counts to the weighted
Pan remainder. Support and truncation hypotheses remain explicit.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- Corrected upper switching cutoff.  Using a ceiling makes the intended
cube-scale coverage an explicit parameter condition rather than a rounding
accident. -/
noncomputable def correctedChenY (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ))

/-- The base candidates for a replacement switching argument.  Unlike the
historical W-candidates, the unit fibre is excluded at the definition level.
The future analytic lower bound must be proved anew for this object. -/
noncomputable def correctedChenCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → ¬ r ∣ N - p)


namespace Internal

/-- The prime factors of a product of distinct primes are exactly the set of
those primes. -/
theorem primeFactors_prod_eq_self {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) : (S.prod id).primeFactors = S := by
  exact MathlibNt.SieveTheory.LiuWeight.primeFactors_prod_eq_self_paperQ hS

end Internal


/-! ## Optimal Selberg upper bound and the main-term identities -/


/-! ## The Pan bridge: lcm merging and compatibility of congruences -/


/-! ## Applying the weighted Pan--Bombieri--Vinogradov input -/


/-! ## Completing the Pan bridge: PanMeanValueUniform ⇒ ChenWeightedPanInput

This section proves only the finite bridge from the `a = 1` base count to `correctedChenBoundingSieve.rem`.
It does not represent the general `p₁p₂` weights in Liu's `eqn-adef`, and therefore does not treat
the noncoprime `R₁` in `eqn-r0`. At the end, the source-faithful signed API is used to assemble
`PanMeanValueUniform`; the paper's `R₁` and the signed main-term bound remain explicit analytic inputs. -/


/-- For a squarefree modulus, `μ(d)² = 1`, since `μ(d) = ±1`. -/
theorem moebius_sq_eq_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
  have hz : (ArithmeticFunction.moebius d : ℤ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_sq, if_pos hd]
  exact_mod_cast hz


end MathlibNt.SieveTheory.SwitchingPrinciple
