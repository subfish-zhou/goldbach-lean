

import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorBadPrimeCorrection

/-!
 # Von Mangoldt conductor change-level correction

For the coefficient `Λ(n)` on the integer interval `[1,N]`, the terms on which
changing a Dirichlet character from level `q` to its conductor can disagree are
prime powers `p^k` with `p ∣ q`.  This gives a polylogarithmic bound for every
correction prefix and, after summing over levels and nonprincipal characters, a
`Q^2` (rather than `N`-times-energy) correction.

The interval starts at zero: all prefix sums below are over `[1,y]`.  No claim is
made here for translated intervals, where a separate count of prime powers in a
short interval would be needed.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The integer coefficient which is `Λ(n)` on positive integers. -/
def vonMangoldtIntegerCoeff (n : ℤ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n.toNat : ℂ)

/-- Prime powers in `[1,N]` on which level `q` can disagree with its conductor. -/
def vonMangoldtBadSupport (q N : ℕ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) N).filter fun n =>
    ArithmeticFunction.vonMangoldt n.toNat ≠ 0 ∧ ¬ IsCoprime n q

@[simp] theorem mem_vonMangoldtBadSupport {q N : ℕ} {n : ℤ} :
    n ∈ vonMangoldtBadSupport q N ↔
      1 ≤ n ∧ n ≤ N ∧ ArithmeticFunction.vonMangoldt n.toNat ≠ 0 ∧
        ¬ IsCoprime n q := by
  simp [vonMangoldtBadSupport, and_assoc]

/-- The explicit family `p^(k+1)`, with `p ∣ q` prime and
`k < log₂(N)+1`, containing the bad von Mangoldt support. -/
def vonMangoldtBadPrimePowers (q N : ℕ) : Finset ℤ :=
  q.primeFactors.biUnion fun p =>
    (Finset.range (Nat.log2 N + 1)).image fun k => ((p ^ (k + 1) : ℕ) : ℤ)

/-- A bad von Mangoldt integer is literally a power of a prime divisor of the
level. -/
theorem vonMangoldtBadSupport_subset_primePowers
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    vonMangoldtBadSupport q N ⊆ vonMangoldtBadPrimePowers q N := by
  intro n hn
  rw [mem_vonMangoldtBadSupport] at hn
  have hn0 : 0 ≤ n := by omega
  have hnN : n.toNat ≤ N := by omega
  have hpp : IsPrimePow n.toNat :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn.2.2.1
  obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff _).mp hpp
  obtain ⟨r, hrq, hrn⟩ :=
    (not_isCoprime_iff_exists_primeFactor_dvd hq n).mp hn.2.2.2
  have hr : r.Prime := (Nat.mem_primeFactors.mp hrq).1
  have hrn' : r ∣ n.toNat := by
    rw [← Int.toNat_of_nonneg hn0] at hrn
    exact_mod_cast hrn
  have hrp : r ∣ p := by
    rw [← hpow] at hrn'
    exact hr.dvd_of_dvd_pow hrn'
  have hr_eq : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
  have htwo : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
  have hkle : k ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc
      2 ^ k ≤ p ^ k := htwo
      _ = n.toNat := hpow
      _ ≤ N := hnN
  rw [vonMangoldtBadPrimePowers, Finset.mem_biUnion]
  refine ⟨p, hr_eq ▸ hrq, Finset.mem_image.mpr ?_⟩
  refine ⟨k - 1, ?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · rw [Nat.sub_add_cancel hk]
    calc
      ((p ^ k : ℕ) : ℤ) = (n.toNat : ℤ) := by exact_mod_cast hpow
      _ = n := Int.toNat_of_nonneg hn0

/-- The number of distinct prime divisors of `q` is at most `log₂ q` for
positive `q`. -/
theorem card_primeFactors_le_log2 {q : ℕ} (hq : 0 < q) :
    q.primeFactors.card ≤ Nat.log2 q := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  calc
    2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ q.primeFactors, p := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
    _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

/-- Cardinality form of the prime-power compression. -/
theorem card_vonMangoldtBadSupport_le {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (vonMangoldtBadSupport q N).card ≤
      q.primeFactors.card * (Nat.log2 N + 1) := by
  calc
    (vonMangoldtBadSupport q N).card ≤ (vonMangoldtBadPrimePowers q N).card :=
      Finset.card_le_card (vonMangoldtBadSupport_subset_primePowers hq N)
    _ ≤ ∑ p ∈ q.primeFactors,
        ((Finset.range (Nat.log2 N + 1)).image
          fun k => ((p ^ (k + 1) : ℕ) : ℤ)).card := by
      unfold vonMangoldtBadPrimePowers
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ q.primeFactors, (Nat.log2 N + 1) := by
      exact Finset.sum_le_sum fun _ _ =>
        Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = q.primeFactors.card * (Nat.log2 N + 1) := by
      simp [Nat.mul_add]

/-- On `[1,N]`, every von Mangoldt change-level error has norm at most
`2 log N`; outside the explicit bad support it is zero. -/
theorem vonMangoldt_changeLevelError_norm_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {N : ℕ} {n : ℤ}
    (hn : n ∈ Finset.Icc (1 : ℤ) N) :
    ‖conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ ≤
      if n ∈ vonMangoldtBadSupport q N then 2 * Real.log (N : ℝ) else 0 := by
  by_cases hbad : n ∈ vonMangoldtBadSupport q N
  · rw [if_pos hbad]
    have hn0 : 0 ≤ n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hnpos : 0 < n.toNat := by
      have hn1 := (Finset.mem_Icc.mp hn).1
      omega
    have hnN : n.toNat ≤ N := Int.toNat_le.mpr (Finset.mem_Icc.mp hn).2
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n.toNat)
    have hΛN : ArithmeticFunction.vonMangoldt n.toNat ≤ Real.log (N : ℝ) := by
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hnN))
    have he := conductorChangeLevelError_norm_sq_le χ vonMangoldtIntegerCoeff n
    have hb : ‖vonMangoldtIntegerCoeff n‖ =
        ArithmeticFunction.vonMangoldt n.toNat := by
      simp [vonMangoldtIntegerCoeff, abs_of_nonneg hΛ0]
    rw [hb] at he
    nlinarith only [he, hΛ0, hΛN,
      norm_nonneg (conductorChangeLevelError χ vonMangoldtIntegerCoeff n)]
  · rw [if_neg hbad]
    have hm := Finset.mem_Icc.mp hn
    simp only [mem_vonMangoldtBadSupport, hm.1, hm.2, true_and] at hbad
    rcases not_and_or.mp hbad with hΛ | hcop
    · have hcoeff : vonMangoldtIntegerCoeff n = 0 := by
        simp [vonMangoldtIntegerCoeff, not_not.mp hΛ]
      simp [conductorChangeLevelError, hcoeff]
    · exact le_of_eq (norm_eq_zero.mpr
        (conductorChangeLevelError_eq_zero_of_isCoprime χ _ (not_not.mp hcop)))

/-- Every prefix correction for `Λ`, on the interval starting at zero, is
polylogarithmic in `N` and `q`. -/
theorem vonMangoldt_conductorErrorPrefixSquare_le
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (N : ℕ) {y : ℕ} (hy : y ≤ N) :
    conductorErrorPrefixSquare χ vonMangoldtIntegerCoeff 0 y ≤
      (2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  have hsub : Finset.Icc (1 : ℤ) y ⊆ Finset.Icc (1 : ℤ) N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (by exact_mod_cast hy)⟩
  have hnorm : ‖∑ n ∈ Finset.Icc (1 : ℤ) y,
      conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ ≤
      2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
    calc
      ‖∑ n ∈ Finset.Icc (1 : ℤ) y,
          conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ ≤
          ∑ n ∈ Finset.Icc (1 : ℤ) y,
            ‖conductorChangeLevelError χ vonMangoldtIntegerCoeff n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc (1 : ℤ) y,
          if n ∈ vonMangoldtBadSupport q N then 2 * Real.log (N : ℝ) else 0 := by
        exact Finset.sum_le_sum fun n hn =>
          vonMangoldt_changeLevelError_norm_le χ (hsub hn)
      _ ≤ ((vonMangoldtBadSupport q N).card : ℝ) *
          (2 * Real.log (N : ℝ)) := by
        rw [← Finset.sum_filter]
        calc
          (∑ _n ∈ (Finset.Icc (1 : ℤ) y).filter
              (fun n => n ∈ vonMangoldtBadSupport q N), 2 * Real.log (N : ℝ)) =
              (((Finset.Icc (1 : ℤ) y).filter
                (fun n => n ∈ vonMangoldtBadSupport q N)).card : ℝ) *
                (2 * Real.log (N : ℝ)) := by simp
          _ ≤ ((vonMangoldtBadSupport q N).card : ℝ) *
                (2 * Real.log (N : ℝ)) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast Finset.card_le_card (by
                intro n hn
                exact (Finset.mem_filter.mp hn).2)
            · positivity
      _ ≤ (q.primeFactors.card : ℝ) * (Nat.log2 N + 1 : ℝ) *
          (2 * Real.log (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_vonMangoldtBadSupport_le hq N
        · positivity
      _ ≤ (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) *
          (2 * Real.log (N : ℝ)) := by
        gcongr
        exact_mod_cast card_primeFactors_le_log2 hq
      _ = _ := by ring
  unfold conductorErrorPrefixSquare
  simpa using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm

/-- Maximal-prefix version of the preceding bound. -/
theorem vonMangoldt_conductorErrorPrefixMaxSquare_le
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    conductorErrorPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N ≤
      (2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  unfold conductorErrorPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact vonMangoldt_conductorErrorPrefixSquare_le hq χ N
    (by simpa [Finset.mem_range] using hy)

/-- The full `q,χ` correction aggregate is `Q²` times a polylogarithm.  This is
the Λ-specific estimate replacing the general coefficient `N`-times-energy
bound. -/
theorem weighted_vonMangoldt_conductorErrorPrefixMaxSquare_le
    (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ nonprincipalCharacters q,
        conductorErrorPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N) ≤
      (Q : ℝ) ^ 2 *
        (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  let C : ℝ :=
    (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ _χ ∈ nonprincipalCharacters q, C := by
      gcongr with q hq χ hχ
      apply (vonMangoldt_conductorErrorPrefixMaxSquare_le
        (Finset.mem_Icc.mp hq).1 χ N).trans
      unfold C
      gcongr
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact_mod_cast Nat.log_mono_right (Finset.mem_Icc.mp hq).2
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) * C := by
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.sum_const, nsmul_eq_mul]
      have hφ : 0 < q.totient := Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
      have hcard : ((nonprincipalCharacters q).card : ℝ) ≤ q.totient := by
        have hchars : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
          have horth := charOrthSum (Finset.mem_Icc.mp hq).1 (1 : ZMod q) 1
          have hc : ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℂ) =
              (q.totient : ℂ) := by simpa using horth
          exact_mod_cast hc
        exact_mod_cast (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq
          (by simpa using hchars)
      have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast (Finset.mem_Icc.mp hq).2
      calc
        (q : ℝ) / q.totient * ((nonprincipalCharacters q).card * C) ≤
            (q : ℝ) / q.totient * ((q.totient : ℝ) * C) := by
          gcongr
        _ = (q : ℝ) * C := by field_simp
        _ ≤ (Q : ℝ) * C := mul_le_mul_of_nonneg_right hqQ hC
    _ = ((Finset.Icc 1 Q).card : ℝ) * ((Q : ℝ) * C) := by simp
    _ ≤ (Q : ℝ) * ((Q : ℝ) * C) := by
      apply mul_le_mul_of_nonneg_right
      · norm_cast
        simp
      · positivity
    _ = _ := by unfold C; ring

/-- Λ-specific all-character nonprincipal maximal reduction: the primitive
conductor ledger plus the now-closed `Q² polylog` correction. -/
theorem weighted_allCharacter_nonprincipal_vonMangoldt_prefix_ledger
    (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ nonprincipalCharacters q,
        characterPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N) ≤
      2 * (∑ d ∈ Finset.Icc 2 Q, imprimitiveConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare vonMangoldtIntegerCoeff 0 N d ψ) +
      2 * (Q : ℝ) ^ 2 *
        (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  have hgroup := weighted_sum_nonprincipal_by_conductor Q
    (fun d ψ => primitiveCharacterPrefixMaxSquare vonMangoldtIntegerCoeff 0 N d ψ)
  have herr := weighted_vonMangoldt_conductorErrorPrefixMaxSquare_le N Q
  calc
    _ ≤ 2 * (∑ d ∈ Finset.Icc 2 Q, imprimitiveConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare vonMangoldtIntegerCoeff 0 N d ψ) +
        2 * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q,
            conductorErrorPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N) := by
      calc
        _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ nonprincipalCharacters q,
              2 * (primitiveCharacterPrefixMaxSquare vonMangoldtIntegerCoeff 0 N
                  χ.conductor (conductorPrimitiveCharacter χ) +
                conductorErrorPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N) := by
          gcongr with q hq χ hχ
          exact characterPrefixMaxSquare_le_conductor_add_error χ
            vonMangoldtIntegerCoeff 0 N
        _ = 2 * (∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ nonprincipalCharacters q,
                  primitiveCharacterPrefixMaxSquare vonMangoldtIntegerCoeff 0 N
                    χ.conductor (conductorPrimitiveCharacter χ)) +
            2 * (∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ nonprincipalCharacters q,
                  conductorErrorPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          ring_nf
        _ = _ := by rw [hgroup]
    _ ≤ _ := by
      nlinarith only [herr]

end

end AnalyticNumberTheory.LargeSieve
