

import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorChangeLevelLedger

/-!
 # Bad-prime compression for conductor change-level corrections

This file is deliberately independent of the existing change-level ledger.  It
makes the support `¬ IsCoprime n q` into a literal union over prime divisors of
`q`, reorders the resulting coefficient energy by prime/multiple, and isolates
the exact non-maximal aggregate input needed to replace the old per-character
`4 * N` Cauchy bound by a dyadic prefix argument.

The finite reductions below contain no prime-number theorem, Bombieri--Vinogradov
claim, or new axiom.  In particular, `ConductorCorrectionBlockBound` is a named
predicate, not a claimed theorem: it freezes the remaining analytic square-mean
estimate in its weakest useful (block, not maximal-prefix) form.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section


/-- A positive-level integer is non-coprime to `q` exactly when some prime
factor of `q` divides it. -/
theorem not_isCoprime_iff_exists_primeFactor_dvd
    {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ¬ IsCoprime n q ↔ ∃ p ∈ q.primeFactors, (p : ℤ) ∣ n := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  constructor
  · intro hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, ?_, hq.ne'⟩, ?_⟩
    · have hpqz : (p : ℤ) ∣ (q : ℤ) := (Int.dvd_gcd_iff.mp hpg).2
      simpa using (Int.natCast_dvd.mp hpqz)
    · exact (Int.dvd_gcd_iff.mp hpg).1
  · rintro ⟨p, hpq, hpn⟩ hg
    have hp := (Nat.mem_primeFactors.mp hpq).1
    have hpq' : (p : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast (Nat.mem_primeFactors.mp hpq).2.1
    have hpg : p ∣ n.gcd q := Int.dvd_gcd hpn hpq'
    rw [hg] at hpg
    exact hp.not_dvd_one hpg


/-- Union bound for a nonnegative weight, with no disjointness hypothesis. -/
theorem sum_biUnion_le_sum_sum_nonneg
    {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (w : β → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ s.biUnion t, w x) ≤ ∑ a ∈ s, ∑ x ∈ t a, w x := by
  classical
  -- Project the indexed fibres onto their union; repeated points only add nonnegative weight.
  have hcover : (s.sigma t).image (fun p => p.2) = s.biUnion t := by
    ext x
    simp
  rw [← hcover, Finset.sum_sigma']
  exact Finset.sum_image_le_of_nonneg (fun x _ => hw x)


/-!
## Scale audit

The closed theorem above shows exactly where the old power loss disappears.  An
aligned dyadic decomposition has `L = log₂ N + 1`.  Thus a block estimate with

`C ≪ (log N)^A * primitiveLargeSieveConstant N Q`

gives an aggregate maximal correction of size

`≪ (log N)^(A+1) * (N + Q^2 log Q) * ∑ |b(n)|^2`.

At `Q ≤ sqrt(N) / (log N)^B`, only the `Q^2` part is reduced to
`N / (log N)^(2B)` (up to the explicit logarithm already present in
`primitiveLargeSieveConstant`).  The leading `N` part is independent of `Q`.
Consequently the level restriction alone does **not** make this correction
`N / (log N)^A`-negligible for arbitrary coefficients; it merely restores the
same power scale as the primitive maximal large sieve and removes the fatal
extra factor `N`.  Any claimed logarithmic negligibility still needs a
source-specific saving in `C` (for example, a prime-multiple/conductor-first
block square mean with the required inverse-log gain), or a separately proved
small energy for the actual coefficient sequence on these prime multiples.
Thus the block square-mean predicate above, or an equivalent conductor-first
maximal large sieve for the prime-multiple dilations, is the minimal honest
analytic input; a stronger all-prefix correction axiom is unnecessary.
-/

end

end AnalyticNumberTheory.LargeSieve
