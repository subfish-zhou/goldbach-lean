import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimeAPPartialSummation

/-!
# Elementary source closure for prime-AP partial summation

This module discharges the higher-prime-power term by a literal finite support
count.  It also records the minimal one-dimensional hypotheses needed for the
global PNT and Chebyshev-to-`li` sources.  No AP or Bombieri--Vinogradov
conclusion is assumed in either source contract.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- Nonprime support of `Λ` through `N`. -/
def higherPrimePowerSupport (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n =>
    ¬ n.Prime ∧ ArithmeticFunction.vonMangoldt n ≠ 0

/-- A finite family containing every higher prime power through `N`: bases up
through `√N`, and exponents up through `log₂ N`. -/
def higherPrimePowerEnvelope (N : ℕ) : Finset ℕ :=
  ((Finset.range (N.sqrt + 1)).product
    (Finset.range (Nat.log2 N + 1))).image fun pk => pk.1 ^ (pk.2 + 2)

lemma higherPrimePowerSupport_subset_envelope (N : ℕ) :
    higherPrimePowerSupport N ⊆ higherPrimePowerEnvelope N := by
  intro n hn
  rw [higherPrimePowerSupport, Finset.mem_filter] at hn
  obtain ⟨p, k, hp, hk, hpow⟩ :=
    (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn.2.2)
  have hk2 : 2 ≤ k := by
    have hk1 : k ≠ 1 := by
      intro h
      subst k
      simp only [pow_one] at hpow
      exact hn.2.1 (hpow ▸ hp)
    omega
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn.1)
  have hp2k : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
  have hpsqrt : p ≤ N.sqrt := by
    rw [Nat.le_sqrt']
    calc
      p ^ 2 ≤ p ^ k := hp2k
      _ = n := hpow
      _ ≤ N := hnN
  have hklog : k ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc
      2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = n := hpow
      _ ≤ N := hnN
  rw [higherPrimePowerEnvelope, Finset.mem_image]
  refine ⟨(p, k - 2), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpsqrt),
      Finset.mem_range.mpr (by omega)⟩
  · simp only
    rw [Nat.sub_add_cancel hk2, hpow]

/-- There are at most `(√N+1)(log₂N+1)` nonprime points in the support of `Λ`.
This is the explicit `k ≥ 2 ⇒ p ≤ √N` count. -/
theorem card_higherPrimePowerSupport_le (N : ℕ) :
    (higherPrimePowerSupport N).card ≤
      (N.sqrt + 1) * (Nat.log2 N + 1) := by
  calc
    (higherPrimePowerSupport N).card ≤ (higherPrimePowerEnvelope N).card :=
      Finset.card_le_card (higherPrimePowerSupport_subset_envelope N)
    _ ≤ (((Finset.range (N.sqrt + 1)).product
        (Finset.range (Nat.log2 N + 1))).card) := Finset.card_image_le
    _ = _ := by simp

private lemma vonMangoldt_zero_local : ArithmeticFunction.vonMangoldt 0 = 0 := by
  simp only [ArithmeticFunction.map_zero]

/-- The von Mangoldt coefficient through `N` has norm at most `log N`. -/
lemma lambda_norm_le_log_of_le {n N : ℕ} (hn : n ≤ N) (hN : 2 ≤ N) :
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

/-- Uniform explicit correction bound, independent of modulus and residue. -/
theorem norm_lambdaPrimePowerCorrection_le_explicit
    {y N q a : ℕ} (hy : y ≤ N) :
    ‖lambdaPrimePowerCorrection y q a‖ ≤
      ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  by_cases hN : 2 ≤ N
  · have hlog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    rw [lambdaPrimePowerCorrection_eq_nonprime_sum]
    calc
      _ ≤ ∑ n ∈ Finset.range (y + 1),
          ‖if (n : ZMod q) = (a : ZMod q) ∧ ¬ n.Prime then lambdaNatCoeff n else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (y + 1),
          if n ∈ higherPrimePowerSupport N then Real.log (N : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n ≤ N :=
          (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hy
        by_cases hr : (n : ZMod q) = (a : ZMod q) ∧ ¬ n.Prime
        · rw [if_pos hr]
          by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
          · simp [lambdaNatCoeff, hΛ, higherPrimePowerSupport]
          · rw [if_pos]
            · exact lambda_norm_le_log_of_le hnN hN
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
                (Nat.lt_succ_iff.mpr hnN), hr.2, hΛ⟩
        · simp only [if_neg hr, norm_zero]
          by_cases hm : n ∈ higherPrimePowerSupport N <;> simp [hm, hlog]
      _ ≤ ((higherPrimePowerSupport N).card : ℝ) * Real.log (N : ℝ) := by
        rw [← Finset.sum_filter]
        calc
          (∑ _n ∈ (Finset.range (y + 1)).filter
              (fun n => n ∈ higherPrimePowerSupport N), Real.log (N : ℝ)) =
              (((Finset.range (y + 1)).filter
                (fun n => n ∈ higherPrimePowerSupport N)).card : ℝ) *
                Real.log (N : ℝ) := by simp
          _ ≤ ((higherPrimePowerSupport N).card : ℝ) * Real.log (N : ℝ) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast Finset.card_le_card (by
                intro n hn
                exact (Finset.mem_filter.mp hn).2)
            · exact hlog
      _ ≤ ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_higherPrimePowerSupport_le N
        · exact hlog

  · have hNle : N ≤ 1 := by omega
    have hcorr : lambdaPrimePowerCorrection y q a = 0 := by
      rw [lambdaPrimePowerCorrection_eq_nonprime_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hn1 : n ≤ 1 :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans (hy.trans hNle)
      have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
        interval_cases n
        · exact vonMangoldt_zero_local
        · exact ArithmeticFunction.vonMangoldt_apply_one
      simp [lambdaNatCoeff, hΛ]
    rw [hcorr, norm_zero]
    interval_cases N <;> norm_num

/-- Prefix/residue maximum inherits the same modulus-free explicit bound. -/
theorem lambdaPrimePowerCorrectionPrefixMaxError_le_explicit (N q : ℕ) :
    lambdaPrimePowerCorrectionPrefixMaxError N q ≤
      ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  unfold lambdaPrimePowerCorrectionPrefixMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨p, hp, rfl⟩
  · positivity
  · rcases Finset.mem_product.mp hp with ⟨hy, ha⟩
    exact norm_lambdaPrimePowerCorrection_le_explicit
      (Nat.le_of_lt_succ (Finset.mem_range.mp hy))

/-- The explicit modulus-free majorant for the higher-prime-power correction. -/
def primePowerCorrectionExplicitBound (N : ℕ) : ℝ :=
  ((N.sqrt + 1 : ℕ) : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)

/-- Summing the residue maximum over any initial modulus interval costs only its
cardinality.  In particular there is no hidden residue-class factor. -/
theorem sum_lambdaPrimePowerCorrectionPrefixMaxError_le
    (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, lambdaPrimePowerCorrectionPrefixMaxError N q) ≤
      (Q : ℝ) * primePowerCorrectionExplicitBound N := by
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, primePowerCorrectionExplicitBound N := by
      exact Finset.sum_le_sum fun q _ =>
        lambdaPrimePowerCorrectionPrefixMaxError_le_explicit N q
    _ = (Q : ℝ) * primePowerCorrectionExplicitBound N := by simp

/-- Literal Standard-BV-range specialization of the preceding elementary
estimate. -/
theorem sum_lambdaPrimePowerCorrection_standardBVRange_le (N : ℕ) (B : ℝ) :
    (∑ q ∈ Finset.Icc 1
        (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
      lambdaPrimePowerCorrectionPrefixMaxError N q) ≤
      (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B : ℝ) *
        primePowerCorrectionExplicitBound N :=
  sum_lambdaPrimePowerCorrectionPrefixMaxError_le N _

/-- Once the elementary scalar majorant fits in an `N/log^A N` budget, the
whole prime-power contribution on the genuine Standard-BV range fits in the
same budget.  This theorem performs the finite `q,residue,prefix` bookkeeping;
its premise is purely one-dimensional. -/
theorem sum_lambdaPrimePowerCorrection_standardBVRange_payable
    {N : ℕ} {A B C : ℝ}
    (hpay :
      (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B : ℝ) *
          primePowerCorrectionExplicitBound N ≤
        C * (N : ℝ) / Real.log N ^ A) :
    (∑ q ∈ Finset.Icc 1
        (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
      lambdaPrimePowerCorrectionPrefixMaxError N q) ≤
        C * (N : ℝ) / Real.log N ^ A :=
  (sum_lambdaPrimePowerCorrection_standardBVRange_le N B).trans hpay

/-- The two genuinely global source terms left by partial summation: the
principal PNT prefix at modulus one, after Abel amplification, and the scalar
discrete-main-to-genuine-`li` discrepancy. -/
def globalPartialSummationSource (N : ℕ) : ℝ :=
  discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 +
    globalChebyshevToLiSourcePrefixMaxError N

/-- Minimal source contract.  It is a statement about one scalar sequence of
`N`, with one common eventual threshold.  It mentions neither residue classes,
AP errors, characters, modulus ranges, nor a BV conclusion. -/
def GlobalChebyshevToLiPrincipalPNTSourceContract : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
        globalPartialSummationSource N ≤
          C * (N : ℝ) / Real.log N ^ A

/-- The one-dimensional contract closes exactly the global source term in the
partial-summation bridge, with no AP/BV assertion frozen into the hypothesis. -/
theorem globalPartialSummationSource_payable
    (hsource : GlobalChebyshevToLiPrincipalPNTSourceContract) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
          discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 +
              globalChebyshevToLiSourcePrefixMaxError N ≤
            C * (N : ℝ) / Real.log N ^ A := by
  intro A hA
  simpa [GlobalChebyshevToLiPrincipalPNTSourceContract,
    globalPartialSummationSource] using hsource A hA

end

end AnalyticNumberTheory.LargeSieve
