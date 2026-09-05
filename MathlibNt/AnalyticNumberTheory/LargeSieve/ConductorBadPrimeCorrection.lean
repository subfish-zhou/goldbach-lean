

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

/-- Multiples of one candidate bad prime in the ambient integer interval. -/
def conductorBadPrimeMultiples (p : ℕ) (M : ℤ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc (M + 1) (M + N)).filter (fun n => (p : ℤ) ∣ n)

@[simp] theorem mem_conductorBadPrimeMultiples {p : ℕ} {M n : ℤ} {N : ℕ} :
    n ∈ conductorBadPrimeMultiples p M N ↔
      M + 1 ≤ n ∧ n ≤ M + N ∧ (p : ℤ) ∣ n := by
  simp [conductorBadPrimeMultiples, and_assoc]

/-- The union of the prime-multiple fibres attached to a positive level. -/
def conductorBadPrimeUnion (q : ℕ) (M : ℤ) (N : ℕ) : Finset ℤ :=
  q.primeFactors.biUnion (fun p => conductorBadPrimeMultiples p M N)

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

/-- Exact support decomposition into bad-prime/multiple fibres. -/
theorem conductorBadSupport_eq_biUnion_primeMultiples
    {q : ℕ} (hq : 0 < q) (M : ℤ) (N : ℕ) :
    conductorBadSupport q M N = conductorBadPrimeUnion q M N := by
  ext n
  simp only [mem_conductorBadSupport, conductorBadPrimeUnion, Finset.mem_biUnion,
    mem_conductorBadPrimeMultiples]
  rw [not_isCoprime_iff_exists_primeFactor_dvd hq n]
  aesop

/-- Union bound for a nonnegative weight, with no disjointness hypothesis. -/
theorem sum_biUnion_le_sum_sum_nonneg
    {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (w : β → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ s.biUnion t, w x) ≤ ∑ a ∈ s, ∑ x ∈ t a, w x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc
        (∑ x ∈ t a ∪ s.biUnion t, w x) ≤
            (∑ x ∈ t a, w x) + ∑ x ∈ s.biUnion t, w x := by
          have hu := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := w)
          have hi : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, w x :=
            Finset.sum_nonneg fun x _ => hw x
          linarith
        _ ≤ (∑ x ∈ t a, w x) + ∑ b ∈ s, ∑ x ∈ t b, w x := by
          gcongr

/-- The bad-support coefficient energy is bounded by the sum of the energies on
prime-multiple fibres.  This is the useful support compression before any
character or modulus Cauchy inequality is taken. -/
theorem conductorBadSupport_energy_le_primeMultiples
    {q : ℕ} (hq : 0 < q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2) ≤
      ∑ p ∈ q.primeFactors,
        ∑ n ∈ conductorBadPrimeMultiples p M N, ‖b n‖ ^ 2 := by
  rw [conductorBadSupport_eq_biUnion_primeMultiples hq]
  exact sum_biUnion_le_sum_sum_nonneg _ _ _ (fun n => sq_nonneg ‖b n‖)

/-- Total level/character weight attached to one bad prime.  The definition
retains exact level weights and exact nonprincipal-character cardinalities. -/
def badPrimeLevelCharacterWeight (Q p : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q with p ∈ q.primeFactors,
    ((q : ℝ) / (q.totient : ℝ)) * (nonprincipalCharacters q).card

/-- Prime-first form of the elementary bad-support energy majorant.  The right
side is already grouped by multiples of `p`; no character-dependent `4*N`
factor has yet been introduced. -/
theorem weighted_badSupport_energy_le_primeFirst
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ _χ ∈ nonprincipalCharacters q,
            ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2) ≤
      ∑ p ∈ Finset.Icc 2 Q,
        badPrimeLevelCharacterWeight Q p *
          ∑ n ∈ conductorBadPrimeMultiples p M N, ‖b n‖ ^ 2 := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q,
        (((q : ℝ) / (q.totient : ℝ)) *
          (nonprincipalCharacters q).card) *
            ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro q hq
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        (((q : ℝ) / (q.totient : ℝ)) *
          (nonprincipalCharacters q).card) *
            ∑ p ∈ q.primeFactors,
              ∑ n ∈ conductorBadPrimeMultiples p M N, ‖b n‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left
          · exact conductorBadSupport_energy_le_primeMultiples
              (Finset.mem_Icc.mp hq).1 b M N
          · positivity
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ p ∈ Finset.Icc 2 Q,
        if p ∈ q.primeFactors then
          (((q : ℝ) / (q.totient : ℝ)) *
            (nonprincipalCharacters q).card) *
              ∑ n ∈ conductorBadPrimeMultiples p M N, ‖b n‖ ^ 2
        else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum, ← Finset.sum_filter]
          apply Finset.sum_subset
          · intro p hp
            have hpf := Nat.mem_primeFactors.mp hp
            rw [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨hpf.1.two_le, (Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 hpf.2.1).trans
              (Finset.mem_Icc.mp hq).2⟩, hp⟩
          · intro p hpQ hpnot
            simp only [Finset.mem_filter] at hpQ
            exact (hpnot hpQ.2).elim
    _ = ∑ p ∈ Finset.Icc 2 Q, ∑ q ∈ Finset.Icc 1 Q,
        if p ∈ q.primeFactors then
          (((q : ℝ) / (q.totient : ℝ)) *
            (nonprincipalCharacters q).card) *
              ∑ n ∈ conductorBadPrimeMultiples p M N, ‖b n‖ ^ 2
        else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [badPrimeLevelCharacterWeight, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hpq : p ∈ q.primeFactors <;> simp [hpq, mul_assoc]

/-- Squared correction on one interval block. -/
def conductorCorrectionBlockSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (A : ℤ) (L : ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc (A + 1) (A + L), conductorChangeLevelError χ b n‖ ^ 2

/-- The genuine remaining analytic input after bad-prime compression and dyadic
prefix decomposition.  It is only a non-maximal aggregate square-mean estimate
for a finite family of interval blocks; it does not assume the desired prefix
maximum.  A large-sieve proof should establish this after rewriting each block
by prime multiples (or by conductor/cofactor Möbius dilation). -/
def ConductorCorrectionBlockBound
    {ι : Type*} [Fintype ι]
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ)
    (blockStart : ι → ℤ) (blockLength : ι → ℕ) (C : ℝ) : Prop :=
  (∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q,
          conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i)) ≤
    C * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2

/-- Finite Rademacher--Menshov transfer for the change-level correction.  This
is the advertised replacement for applying full-interval Cauchy separately to
every character: the loss is the number `L` of blocks in one prefix, while the
analytic input is an aggregate block square mean. -/
theorem weighted_conductorError_prefixMax_le_of_blockBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℤ → ℂ) (M : ℤ) (N Q L : ℕ)
    (blockStart : ι → ℤ) (blockLength : ι → ℕ)
    (prefixBlocks : ℕ → Finset ι)
    (hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
      (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
        ∑ i ∈ prefixBlocks y,
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), f n)
    (hcard : ∀ y ∈ Finset.range (N + 1), (prefixBlocks y).card ≤ L)
    {C : ℝ} (hC : ConductorCorrectionBlockBound b M N Q blockStart blockLength C) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q,
          conductorErrorPrefixMaxSquare χ b M N) ≤
      (L : ℝ) * C *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have hmax : ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      conductorErrorPrefixMaxSquare χ b M N ≤
        (L : ℝ) * ∑ i : ι,
          conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i) := by
    intro q χ
    unfold conductorErrorPrefixMaxSquare
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    unfold conductorErrorPrefixSquare
    rw [hdecomp y hy (fun n => conductorChangeLevelError χ b n)]
    calc
      ‖∑ i ∈ prefixBlocks y,
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), conductorChangeLevelError χ b n‖ ^ 2 ≤
        ((prefixBlocks y).card : ℝ) *
          ∑ i ∈ prefixBlocks y,
            conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i) := by
              exact norm_finset_sum_sq_le_card_mul_sum_norm_sq _ _
      _ ≤ (L : ℝ) * ∑ i ∈ prefixBlocks y,
            conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i) := by
              apply mul_le_mul_of_nonneg_right
              · exact_mod_cast hcard y hy
              · exact Finset.sum_nonneg fun i _ => sq_nonneg _
      _ ≤ (L : ℝ) * ∑ i : ι,
            conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i) := by
              apply mul_le_mul_of_nonneg_left
              · exact Finset.sum_le_univ_sum_of_nonneg
                  (fun i => sq_nonneg _)
              · positivity
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q,
          ((L : ℝ) * ∑ i : ι,
            conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i)) := by
              gcongr with q hq χ hχ
              exact hmax q χ
    _ = (L : ℝ) * ∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q,
          conductorCorrectionBlockSquare χ b (blockStart i) (blockLength i) := by
            calc
              _ = ∑ q ∈ Finset.Icc 1 Q, ∑ i : ι,
                    ∑ χ ∈ nonprincipalCharacters q,
                      (L : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
                        conductorCorrectionBlockSquare χ b
                          (blockStart i) (blockLength i)) := by
                    apply Finset.sum_congr rfl
                    intro q hq
                    simp only [Finset.mul_sum]
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro χ hχ
                    ring
              _ = ∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
                    ∑ χ ∈ nonprincipalCharacters q,
                      (L : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
                        conductorCorrectionBlockSquare χ b
                          (blockStart i) (blockLength i)) := by
                    rw [Finset.sum_comm]
              _ = _ := by
                    simp only [Finset.mul_sum]
    _ ≤ (L : ℝ) * (C *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by ring

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
