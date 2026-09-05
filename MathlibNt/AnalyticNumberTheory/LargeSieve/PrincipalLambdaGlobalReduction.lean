import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimeAPSourceClosure
import MathlibNt.AnalyticNumberTheory.LargeSieve.VonMangoldtConductorCorrection

/-!
# Reduction of every principal character to the global PNT source

The principal character at level `q` deletes exactly the von Mangoldt mass on
prime powers `p^k` with `p ∣ q`.  This module makes that deletion literal,
bounds it by `ω(q) (log₂ N + 1) log N`, sums the correction over `q ≤ Q`, and
feeds the modulus-one source contract into the prime-AP partial-summation bridge.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- The non-coprime von Mangoldt support through `N`. -/
def principalBadLambdaSupport (q N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n =>
    ArithmeticFunction.vonMangoldt n ≠ 0 ∧ ¬ n.Coprime q

/-- The explicit prime-power envelope indexed by `p ∣ q` and the exponent. -/
def principalBadPrimePowers (q N : ℕ) : Finset ℕ :=
  q.primeFactors.biUnion fun p =>
    (Finset.range (Nat.log2 N + 1)).image fun k => p ^ (k + 1)

/-- Every non-coprime point supporting `Λ` is `p^k` for a prime divisor of `q`. -/
theorem principalBadLambdaSupport_subset_primePowers
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    principalBadLambdaSupport q N ⊆ principalBadPrimePowers q N := by
  intro n hn
  rw [principalBadLambdaSupport, Finset.mem_filter] at hn
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn.1)
  obtain ⟨p, k, hp, hk, hpow⟩ :=
    (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn.2.1)
  have hgcd : n.gcd q ≠ 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one] using hn.2.2
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hgcd
  have hrn : r ∣ n := hrg.trans (Nat.gcd_dvd_left n q)
  have hrq : r ∣ q := hrg.trans (Nat.gcd_dvd_right n q)
  have hrp : r ∣ p := by
    rw [← hpow] at hrn
    exact hr.dvd_of_dvd_pow hrn
  have hr_eq : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
  have hklog : k ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc
      2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = n := hpow
      _ ≤ N := hnN
  rw [principalBadPrimePowers, Finset.mem_biUnion]
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, ?_, hq.ne'⟩, Finset.mem_image.mpr ?_⟩
  · simpa [hr_eq] using hrq
  · refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hk, hpow]

/-- There are at most `ω(q)(log₂ N+1)` bad prime powers through `N`. -/
theorem card_principalBadLambdaSupport_le
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (principalBadLambdaSupport q N).card ≤
      q.primeFactors.card * (Nat.log2 N + 1) := by
  calc
    (principalBadLambdaSupport q N).card ≤ (principalBadPrimePowers q N).card :=
      Finset.card_le_card (principalBadLambdaSupport_subset_primePowers hq N)
    _ ≤ ∑ p ∈ q.primeFactors,
        ((Finset.range (Nat.log2 N + 1)).image fun k => p ^ (k + 1)).card := by
      unfold principalBadPrimePowers
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ q.primeFactors, (Nat.log2 N + 1) := by
      exact Finset.sum_le_sum fun _ _ =>
        Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = _ := by simp [Nat.mul_add]

/-- The mass deleted from the principal character at modulus `q`. -/
def principalBadLambdaMass (y q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (y + 1),
    if n.Coprime q then 0 else lambdaNatCoeff n

/-- Literal partition of the global von Mangoldt prefix into coprime and bad mass. -/
theorem coprimeLambdaPrefix_one_eq_add_badMass (y q : ℕ) :
    coprimeLambdaPrefix y 1 =
      coprimeLambdaPrefix y q + principalBadLambdaMass y q := by
  unfold coprimeLambdaPrefix principalBadLambdaMass
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hone : n.Coprime 1 := Nat.coprime_one_right n
  by_cases h : n.Coprime q
  · simp only [if_pos hone, if_pos h, add_zero]
  · simp only [if_pos hone, if_neg h, zero_add]

private lemma lambda_norm_le_log_of_le_global
    {n N : ℕ} (hn : n ≤ N) (hN : 2 ≤ N) :
    ‖lambdaNatCoeff n‖ ≤ Real.log (N : ℝ) := by
  by_cases hnz : n = 0
  · subst n
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    simp [lambdaNatCoeff, Real.log_nonneg hN1]
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [lambdaNatCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0]
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.strictMonoOn_log.monotoneOn hnpos hNpos (by exact_mod_cast hn))

/-- Explicit `ω(q)` bound for the deleted mass. -/
theorem norm_principalBadLambdaMass_le_omega
    {y N q : ℕ} (hq : 0 < q) (hy : y ≤ N) (hN : 2 ≤ N) :
    ‖principalBadLambdaMass y q‖ ≤
      (q.primeFactors.card : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  unfold principalBadLambdaMass
  calc
    _ ≤ ∑ n ∈ Finset.range (y + 1),
        ‖if n.Coprime q then 0 else lambdaNatCoeff n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (y + 1),
        if n ∈ principalBadLambdaSupport q N then Real.log (N : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN : n ≤ N :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hy
      have hlog : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
      by_cases hc : n.Coprime q
      · simp only [if_pos hc, norm_zero]
        split_ifs <;> positivity
      · by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
        · simp only [if_neg hc, lambdaNatCoeff, hΛ, Complex.ofReal_zero, norm_zero]
          split_ifs <;> positivity
        · rw [if_neg hc, if_pos]
          · exact lambda_norm_le_log_of_le_global hnN hN
          · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
              (Nat.lt_succ_iff.mpr hnN), hΛ, hc⟩
    _ ≤ ((principalBadLambdaSupport q N).card : ℝ) * Real.log (N : ℝ) := by
      rw [← Finset.sum_filter]
      calc
        (∑ _n ∈ (Finset.range (y + 1)).filter
            (fun n => n ∈ principalBadLambdaSupport q N), Real.log (N : ℝ)) =
            (((Finset.range (y + 1)).filter
              (fun n => n ∈ principalBadLambdaSupport q N)).card : ℝ) *
              Real.log (N : ℝ) := by simp
        _ ≤ ((principalBadLambdaSupport q N).card : ℝ) * Real.log (N : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_le_card (by
              intro n hn
              exact (Finset.mem_filter.mp hn).2)
          · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    _ ≤ (q.primeFactors.card : ℝ) * (Nat.log2 N + 1 : ℝ) *
        Real.log (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_principalBadLambdaSupport_le hq N
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))

/-- The same correction with the elementary `ω(q) ≤ log₂ q` substitution. -/
theorem norm_principalBadLambdaMass_le_log2
    {y N q : ℕ} (hq : 0 < q) (hy : y ≤ N) (hN : 2 ≤ N) :
    ‖principalBadLambdaMass y q‖ ≤
      (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  refine (norm_principalBadLambdaMass_le_omega hq hy hN).trans ?_
  gcongr
  exact_mod_cast card_primeFactors_le_log2 hq

/-- Pointwise principal error at `q` is the global error plus bad prime powers. -/
theorem norm_principalLambdaMainError_le_global_add_bad
    {y N q : ℕ} (hq : 0 < q) (hy : y ≤ N) (hN : 2 ≤ N) :
    ‖principalLambdaMainError y q‖ ≤
      ‖principalLambdaMainError y 1‖ +
        (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  have hid : principalLambdaMainError y q =
      principalLambdaMainError y 1 - principalBadLambdaMass y q := by
    unfold principalLambdaMainError
    rw [coprimeLambdaPrefix_one_eq_add_badMass y q]
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans
    (add_le_add le_rfl (norm_principalBadLambdaMass_le_log2 hq hy hN))

/-- Uniform principal reduction for every positive modulus. -/
theorem principalLambdaPrefixMaxError_le_global_add_bad
    {N q : ℕ} (hq : 0 < q) (hN : 2 ≤ N) :
    principalLambdaPrefixMaxError N q ≤
      principalLambdaPrefixMaxError N 1 +
        (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  unfold principalLambdaPrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  refine (norm_principalLambdaMainError_le_global_add_bad hq
    (Nat.le_of_lt_succ (Finset.mem_range.mp hy)) hN).trans ?_
  exact add_le_add
    (Finset.le_max'
      ((Finset.range (N + 1)).image
        (fun y => ‖principalLambdaMainError y 1‖)) _
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)) le_rfl

/-- Summing all principal errors through `Q` costs one copy of the global error
per modulus and an explicit `Q log₂Q log₂N log N` scalar. -/
theorem sum_principalLambdaPrefixMaxError_le_global
    {N Q : ℕ} (hN : 2 ≤ N) :
    (∑ q ∈ Finset.Icc 1 Q, principalLambdaPrefixMaxError N q) ≤
      (Q : ℝ) * principalLambdaPrefixMaxError N 1 +
        (Q : ℝ) * ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) *
          Real.log (N : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        (principalLambdaPrefixMaxError N 1 +
          (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      refine (principalLambdaPrefixMaxError_le_global_add_bad
        (Finset.mem_Icc.mp hq).1 hN).trans ?_
      gcongr
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact_mod_cast Nat.log_mono_right (Finset.mem_Icc.mp hq).2
    _ = ((Finset.Icc 1 Q).card : ℝ) *
        (principalLambdaPrefixMaxError N 1 +
          (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) *
        (principalLambdaPrefixMaxError N 1 +
          (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · norm_cast
        simp
      · exact add_nonneg (by
          unfold principalLambdaPrefixMaxError
          exact (norm_nonneg (principalLambdaMainError 0 1)).trans (Finset.le_max'
            ((Finset.range (N + 1)).image
              (fun y => ‖principalLambdaMainError y 1‖)) _
            (Finset.mem_image.mpr
              ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))) (by positivity)
    _ = _ := by rw [mul_add]

/-- In a `Q ≤ √N/log^B N` range, the complete bad-prime-power aggregate is
paid once the displayed scalar (with `Q` eliminated) fits the target budget. -/
theorem sum_principal_badCorrection_BVRange_payable
    {N Q : ℕ} {A B C : ℝ} (_hN : 2 ≤ N)
    (hQ : (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B)
    (hscalar :
      (Real.sqrt N / Real.log (N : ℝ) ^ B) *
          ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ≤
        C * (N : ℝ) / Real.log N ^ A) :
    (∑ q ∈ Finset.Icc 1 Q,
      (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ≤
        C * (N : ℝ) / Real.log N ^ A := by
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q,
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact_mod_cast Nat.log_mono_right (Finset.mem_Icc.mp hq).2
    _ = ((Finset.Icc 1 Q).card : ℝ) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) := by simp
    _ ≤ (Q : ℝ) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · norm_cast
        simp
      · positivity
    _ ≤ (Real.sqrt N / Real.log (N : ℝ) ^ B) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ ≤ _ := hscalar

/-- The all-modulus partial-summation bridge with the principal term reduced
literally to the modulus-one PNT error plus bad prime powers. -/
theorem standardPrimeAPPrefixMaxError_le_global_principal_bridge
    {N q : ℕ} (hq : 0 < q) (hN : 2 ≤ N) :
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
      discreteAbelAmplifierPrefixMax N *
        ((q.totient : ℝ)⁻¹ *
            (principalLambdaPrefixMaxError N 1 +
              (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
              ∑ χ ∈ nonprincipalCharacters q,
                lambdaCharacterPrefixMaxAmplitude N q χ) +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourcePrefixMaxError N := by
  refine (standardPrimeAPPrefixMaxError_le_principal_character_bridge hq).trans ?_
  have hA : 0 ≤ discreteAbelAmplifierPrefixMax N := by
    have h0 : 0 ≤ discreteAbelAmplifier 0 := by unfold discreteAbelAmplifier; positivity
    exact h0.trans (by
      unfold discreteAbelAmplifierPrefixMax
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hA
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    exact add_le_add
      (principalLambdaPrefixMaxError_le_global_add_bad hq hN) le_rfl
  · exact le_rfl

/-- The global source contract now feeds the prime-AP bridge for every positive
`q`; only the explicit bad-prime-power term and nonprincipal transforms remain. -/
theorem globalSourceContract_to_all_moduli_primeAPBridge
    (hsource : GlobalChebyshevToLiPrincipalPNTSourceContract) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N → ∀ q : ℕ, 0 < q →
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
          discreteAbelAmplifierPrefixMax N *
            ((q.totient : ℝ)⁻¹ *
                ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
                  ∑ χ ∈ nonprincipalCharacters q,
                    lambdaCharacterPrefixMaxAmplitude N q χ) +
              lambdaPrimePowerCorrectionPrefixMaxError N q) +
            (q.totient : ℝ)⁻¹ * (C * (N : ℝ) / Real.log N ^ A) := by
  intro A hA
  obtain ⟨C, hC, hsourceC⟩ := globalPartialSummationSource_payable hsource A hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsourceC] with N hglobal
  intro hN q hq
  refine (standardPrimeAPPrefixMaxError_le_global_principal_bridge hq hN).trans ?_
  have hφ : 0 ≤ (q.totient : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hA0 : 0 ≤ discreteAbelAmplifierPrefixMax N := by
    have h0 : 0 ≤ discreteAbelAmplifier 0 := by unfold discreteAbelAmplifier; positivity
    exact h0.trans (by
      unfold discreteAbelAmplifierPrefixMax
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
  have hglobal' := hglobal hN
  calc
    _ = discreteAbelAmplifierPrefixMax N *
          ((q.totient : ℝ)⁻¹ *
              ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
                ∑ χ ∈ nonprincipalCharacters q,
                  lambdaCharacterPrefixMaxAmplitude N q χ) +
            lambdaPrimePowerCorrectionPrefixMaxError N q) +
        (q.totient : ℝ)⁻¹ *
          (discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 +
            globalChebyshevToLiSourcePrefixMaxError N) := by ring
    _ ≤ discreteAbelAmplifierPrefixMax N *
          ((q.totient : ℝ)⁻¹ *
              ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
                ∑ χ ∈ nonprincipalCharacters q,
                  lambdaCharacterPrefixMaxAmplitude N q χ) +
            lambdaPrimePowerCorrectionPrefixMaxError N q) +
        (q.totient : ℝ)⁻¹ * (C * (N : ℝ) / Real.log N ^ A) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hglobal' hφ)

end

end AnalyticNumberTheory.LargeSieve
