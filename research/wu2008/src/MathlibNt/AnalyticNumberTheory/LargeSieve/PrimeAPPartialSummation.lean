import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVCharacterOrthogonality
import MathlibNt.SieveTheory.Distribution.BombieriVinogradov

/-!
# Discrete partial summation from Chebyshev AP errors to prime AP errors

This module is deliberately downstream of the proved finite character
orthogonality module.  It does not assume a Bombieri--Vinogradov conclusion.
The only separately packaged source term is the scalar comparison between the
discrete Abel main term and the genuine logarithmic integral.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Inclusive partial sum through `y`. -/
def realPrefix (c : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1), c n

/-- Finite discrete Abel summation, including both endpoints. -/
theorem sum_range_mul_eq_discreteAbel (c w : ℕ → ℝ) (y : ℕ) :
    (∑ n ∈ range (y + 1), w n * c n) =
      w y * realPrefix c y +
        ∑ n ∈ range y, (w n - w (n + 1)) * realPrefix c n := by
  induction y with
  | zero => simp [realPrefix]
  | succ y ih =>
      simp only [Finset.sum_range_succ, realPrefix] at ih ⊢
      rw [ih]
      ring

/-- Reciprocal-log weight with the low endpoint made total. -/
def reciprocalLogWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (Real.log (n : ℝ))⁻¹ else 0

/-- The logarithmically weighted prime increment in one residue class. -/
def primeThetaAPIncrement (q a n : ℕ) : ℝ :=
  if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0

/-- The ordinary prime indicator in one residue class. -/
def primeAPIncrement (q a n : ℕ) : ℝ :=
  if n.Prime ∧ n ≡ a [MOD q] then 1 else 0

/-- The Chebyshev theta-prefix (primes only, weighted by `log p`). -/
def primeThetaAPPrefix (y q a : ℕ) : ℝ :=
  realPrefix (primeThetaAPIncrement q a) y

/-- Multiplication by `1 / log p` removes the prime logarithmic weight. -/
theorem reciprocalLogWeight_mul_primeThetaAPIncrement (q a n : ℕ) :
    reciprocalLogWeight n * primeThetaAPIncrement q a n = primeAPIncrement q a n := by
  unfold reciprocalLogWeight primeThetaAPIncrement primeAPIncrement
  by_cases h : n.Prime ∧ n ≡ a [MOD q]
  · rw [if_pos h, if_pos h]
    have hn2 : 2 ≤ n := h.1.two_le
    rw [if_pos hn2]
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast h.1.one_lt)).ne'
    field_simp
  · simp [h]

/-- Prime counting is the finite sum of the ordinary AP indicators. -/
theorem cast_primesInAP_eq_sum_primeAPIncrement (y q a : ℕ) :
    (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP y q a : ℝ) =
      ∑ n ∈ range (y + 1), primeAPIncrement q a n := by
  simp [MathlibNt.SieveTheory.BombieriVinogradov.primesInAP, primeAPIncrement]

/-- Exact discrete Abel formula for prime counting.  The terms at `0` and `1`
vanish because there are no primes there; no singular logarithm is evaluated. -/
theorem primesInAP_eq_discreteAbel (y q a : ℕ) :
    (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP y q a : ℝ) =
      reciprocalLogWeight y * primeThetaAPPrefix y q a +
        ∑ n ∈ range y,
          (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) *
            primeThetaAPPrefix n q a := by
  rw [cast_primesInAP_eq_sum_primeAPIncrement]
  simp_rw [← reciprocalLogWeight_mul_primeThetaAPIncrement q a]
  exact sum_range_mul_eq_discreteAbel _ _ _

/-- The deterministic main term obtained by applying the same finite Abel
operator to the Chebyshev main prefix `y`. -/
def discreteAbelLiMain (y : ℕ) : ℝ :=
  reciprocalLogWeight y * y +
    ∑ n ∈ range y,
      (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * n

/-- The total variation of the finite Abel operator.  Keeping this exact finite
quantity makes the estimates valid also at `y = 0,1,2`. -/
def discreteAbelAmplifier (y : ℕ) : ℝ :=
  |reciprocalLogWeight y| +
    ∑ n ∈ range y, |reciprocalLogWeight n - reciprocalLogWeight (n + 1)|

/-- Theta error in one reduced residue class. -/
def thetaAPMainError (y q a : ℕ) : ℝ :=
  primeThetaAPPrefix y q a - (q.totient : ℝ)⁻¹ * y

/-- Exact higher-prime-power correction between `ψ` (the von Mangoldt prefix)
and `θ` (the sum of `log p` over primes). -/
def lambdaPrimePowerCorrection (y q a : ℕ) : ℂ :=
  lambdaAPPrefix y q a - (primeThetaAPPrefix y q a : ℂ)

/-- The correction is exactly what must be removed from the von Mangoldt prefix
to leave the prime-only logarithmic weight. -/
theorem lambdaAPPrefix_sub_primePowerCorrection (y q a : ℕ) :
    lambdaAPPrefix y q a - lambdaPrimePowerCorrection y q a =
      (primeThetaAPPrefix y q a : ℂ) := by
  simp [lambdaPrimePowerCorrection]

/-- The correction has the promised arithmetic content: it is precisely the
von Mangoldt mass on non-primes in the residue class (hence, by the support of
`Λ`, on higher prime powers). -/
theorem lambdaPrimePowerCorrection_eq_nonprime_sum (y q a : ℕ) :
    lambdaPrimePowerCorrection y q a =
      ∑ n ∈ range (y + 1),
        if (n : ZMod q) = (a : ZMod q) ∧ ¬ n.Prime then lambdaNatCoeff n else 0 := by
  unfold lambdaPrimePowerCorrection lambdaAPPrefix primeThetaAPPrefix realPrefix
    primeThetaAPIncrement
  rw [Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hr : (n : ZMod q) = (a : ZMod q)
  · have hmod : n ≡ a [MOD q] :=
      (ZMod.natCast_eq_natCast_iff n a q).mp hr
    by_cases hp : n.Prime
    · simp [hr, hmod, hp, lambdaNatCoeff,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hr, hmod, hp]
  · have hnotmod : ¬ n ≡ a [MOD q] := by
      simpa only [ZMod.natCast_eq_natCast_iff] using hr
    simp [hr, hnotmod]

/-- Pointwise conversion of a `ψ` AP error into a `θ` AP error, paying the
higher-prime-power correction explicitly. -/
theorem abs_thetaAPMainError_le_lambda_add_primePower (y q a : ℕ) :
    |thetaAPMainError y q a| ≤
      ‖lambdaAPMainError y q a‖ + ‖lambdaPrimePowerCorrection y q a‖ := by
  have hid : ((thetaAPMainError y q a : ℝ) : ℂ) =
      lambdaAPMainError y q a - lambdaPrimePowerCorrection y q a := by
    unfold thetaAPMainError lambdaAPMainError lambdaPrimePowerCorrection
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hid]
  exact norm_sub_le _ _

/-- The genuine-li source discrepancy.  This is a one-dimensional global
source term, independent of the modulus and residue; no AP conclusion is hidden
in it. -/
def globalChebyshevToLiSourceError (y : ℕ) : ℝ :=
  |discreteAbelLiMain y -
    MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral y|

/-- Absolute-value estimate for the finite Abel operator under a uniform prefix
bound.  This is the discrete partial-summation inequality used below. -/
theorem abs_discreteAbel_le
    (E : ℕ → ℝ) (M : ℝ) (y : ℕ)
    (hE : ∀ n ≤ y, |E n| ≤ M) :
    |reciprocalLogWeight y * E y +
        ∑ n ∈ range y,
          (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n| ≤
      discreteAbelAmplifier y * M := by
  calc
    _ ≤ |reciprocalLogWeight y * E y| +
        ∑ n ∈ range y,
          |(reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _))
    _ ≤ |reciprocalLogWeight y| * M +
        ∑ n ∈ range y,
          |reciprocalLogWeight n - reciprocalLogWeight (n + 1)| * M := by
      simp only [abs_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hE y le_rfl) (abs_nonneg _)
      · exact sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_left (hE n (Nat.le_of_lt (mem_range.mp hn))) (abs_nonneg _)
    _ = _ := by
      unfold discreteAbelAmplifier
      rw [add_mul, sum_mul]

/-- The largest theta-prefix error for one residue through `N`. -/
def thetaAPResiduePrefixMaxError (N q a : ℕ) : ℝ :=
  ((range (N + 1)).image (fun y => |thetaAPMainError y q a|)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem abs_thetaAPMainError_le_residuePrefixMax
    {y N q a : ℕ} (hy : y ≤ N) :
    |thetaAPMainError y q a| ≤ thetaAPResiduePrefixMaxError N q a := by
  unfold thetaAPResiduePrefixMaxError
  exact Finset.le_max'
    ((range (N + 1)).image (fun y : ℕ => |thetaAPMainError y q a|)) _
    (Finset.mem_image.mpr ⟨y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩)

private theorem thetaAPResiduePrefixMaxError_mono
    {y N q a : ℕ} (hy : y ≤ N) :
    thetaAPResiduePrefixMaxError y q a ≤ thetaAPResiduePrefixMaxError N q a := by
  unfold thetaAPResiduePrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
  exact abs_thetaAPMainError_le_residuePrefixMax
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hy)

/-- Exact pointwise discrete partial-summation bound before taking maxima. -/
theorem abs_standardPrimeAPError_le_abel
    {y q a : ℕ} (hq : 0 < q) :
    |MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError y q a| ≤
      discreteAbelAmplifier y * thetaAPResiduePrefixMaxError y q a +
        (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourceError y := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  let E : ℕ → ℝ := fun n => thetaAPMainError n q a
  have hrewrite (n : ℕ) :
      primeThetaAPPrefix n q a = (q.totient : ℝ)⁻¹ * n + E n := by
    dsimp [E]
    unfold thetaAPMainError
    ring
  have heq :
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError y q a =
        (reciprocalLogWeight y * E y +
          ∑ n ∈ range y,
            (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n) +
        (q.totient : ℝ)⁻¹ *
          (discreteAbelLiMain y -
            MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral y) := by
    rw [MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError,
      primesInAP_eq_discreteAbel]
    simp_rw [hrewrite, mul_add]
    rw [sum_add_distrib]
    unfold discreteAbelLiMain
    have hfactor :
        (∑ n ∈ range y,
          (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) *
            ((q.totient : ℝ)⁻¹ * n)) =
        (q.totient : ℝ)⁻¹ *
          ∑ n ∈ range y,
            (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hfactor]
    ring
  rw [heq]
  calc
    _ ≤ |reciprocalLogWeight y * E y +
          ∑ n ∈ range y,
            (reciprocalLogWeight n - reciprocalLogWeight (n + 1)) * E n| +
        |(q.totient : ℝ)⁻¹ *
          (discreteAbelLiMain y -
            MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral y)| :=
      abs_add_le _ _
    _ ≤ discreteAbelAmplifier y * thetaAPResiduePrefixMaxError y q a +
        (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourceError y := by
      apply add_le_add
      · apply abs_discreteAbel_le
        intro n hn
        exact abs_thetaAPMainError_le_residuePrefixMax hn
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hφ)]
        unfold globalChebyshevToLiSourceError
        rfl

/-- Prefix maximum of the explicit higher-prime-power correction. -/
def lambdaPrimePowerCorrectionPrefixMaxError (N q : ℕ) : ℝ :=
  (insert 0 (((range (N + 1)).product
    (AnalyticNumberTheory.Sieve.unitResidues q)).image
      (fun p => ‖lambdaPrimePowerCorrection p.1 q p.2‖))).max' (by simp)

/-- Prefix maximum of the total variation of the Abel kernel. -/
def discreteAbelAmplifierPrefixMax (N : ℕ) : ℝ :=
  ((range (N + 1)).image discreteAbelAmplifier).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Prefix maximum of the one-dimensional genuine-li source discrepancy. -/
def globalChebyshevToLiSourcePrefixMaxError (N : ℕ) : ℝ :=
  ((range (N + 1)).image globalChebyshevToLiSourceError).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private theorem norm_lambdaAPMainError_le_prefixMax
    {y N q a : ℕ} (hy : y ≤ N)
    (ha : a ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    ‖lambdaAPMainError y q a‖ ≤ lambdaAPPrefixMaxError N q := by
  unfold lambdaAPPrefixMaxError
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(y, a), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), ha⟩, rfl⟩)

private theorem norm_primePowerCorrection_le_prefixMax
    {y N q a : ℕ} (hy : y ≤ N)
    (ha : a ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    ‖lambdaPrimePowerCorrection y q a‖ ≤
      lambdaPrimePowerCorrectionPrefixMaxError N q := by
  unfold lambdaPrimePowerCorrectionPrefixMaxError
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(y, a), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), ha⟩, rfl⟩)

private theorem discreteAbelAmplifier_le_prefixMax
    {y N : ℕ} (hy : y ≤ N) :
    discreteAbelAmplifier y ≤ discreteAbelAmplifierPrefixMax N := by
  unfold discreteAbelAmplifierPrefixMax
  exact Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩)

private theorem discreteAbelAmplifier_nonneg (y : ℕ) :
    0 ≤ discreteAbelAmplifier y := by
  unfold discreteAbelAmplifier
  exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem discreteAbelAmplifierPrefixMax_nonneg (N : ℕ) :
    0 ≤ discreteAbelAmplifierPrefixMax N :=
  (discreteAbelAmplifier_nonneg 0).trans
    (discreteAbelAmplifier_le_prefixMax (Nat.zero_le N))

private theorem globalSourceError_le_prefixMax
    {y N : ℕ} (hy : y ≤ N) :
    globalChebyshevToLiSourceError y ≤
      globalChebyshevToLiSourcePrefixMaxError N := by
  unfold globalChebyshevToLiSourcePrefixMaxError
  exact Finset.le_max' _ _ (Finset.mem_image.mpr
    ⟨y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩)

/-- Uniform theta-prefix control obtained from all von Mangoldt AP prefixes and
the explicit higher-prime-power correction. -/
theorem thetaAPResiduePrefixMaxError_le_lambda_add_primePower
    {N q a : ℕ} (ha : a ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    thetaAPResiduePrefixMaxError N q a ≤
      lambdaAPPrefixMaxError N q +
        lambdaPrimePowerCorrectionPrefixMaxError N q := by
  unfold thetaAPResiduePrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  exact (abs_thetaAPMainError_le_lambda_add_primePower y q a).trans
    (add_le_add (norm_lambdaAPMainError_le_prefixMax hyN ha)
      (norm_primePowerCorrection_le_prefixMax hyN ha))

private theorem insertZeroMax_nonneg (S : Finset ℝ) :
    0 ≤ (insert 0 S).max' (by simp) :=
  Finset.le_max' (insert 0 S) 0 (Finset.mem_insert_self 0 S)

private theorem bridgeRHS_nonneg (N q : ℕ) :
    0 ≤ discreteAbelAmplifierPrefixMax N *
        (lambdaAPPrefixMaxError N q +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourcePrefixMaxError N := by
  have hA := discreteAbelAmplifierPrefixMax_nonneg N
  have hL : 0 ≤ lambdaAPPrefixMaxError N q := by
    unfold lambdaAPPrefixMaxError
    exact insertZeroMax_nonneg _
  have hP : 0 ≤ lambdaPrimePowerCorrectionPrefixMaxError N q := by
    unfold lambdaPrimePowerCorrectionPrefixMaxError
    exact insertZeroMax_nonneg _
  have hS : 0 ≤ globalChebyshevToLiSourcePrefixMaxError N :=
    (abs_nonneg _).trans (globalSourceError_le_prefixMax (Nat.zero_le N))
  positivity

/-- Pointwise prime-AP error controlled uniformly by the lambda AP prefix
maximum, prime powers, and the scalar genuine-li source term. -/
theorem abs_standardPrimeAPError_le_prefix_bridge
    {y N q a : ℕ} (hq : 0 < q) (hy : y ≤ N)
    (ha : a ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    |MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError y q a| ≤
      discreteAbelAmplifierPrefixMax N *
        (lambdaAPPrefixMaxError N q +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourcePrefixMaxError N := by
  refine (abs_standardPrimeAPError_le_abel hq).trans ?_
  apply add_le_add
  · have hTheta : 0 ≤ thetaAPResiduePrefixMaxError y q a :=
      (abs_nonneg (thetaAPMainError 0 q a)).trans
        (abs_thetaAPMainError_le_residuePrefixMax (Nat.zero_le y))
    exact mul_le_mul
      (discreteAbelAmplifier_le_prefixMax hy)
      ((thetaAPResiduePrefixMaxError_mono hy).trans
        (thetaAPResiduePrefixMaxError_le_lambda_add_primePower ha))
      hTheta (discreteAbelAmplifierPrefixMax_nonneg N)
  · exact mul_le_mul_of_nonneg_left (globalSourceError_le_prefixMax hy)
      (inv_nonneg.mpr (Nat.cast_nonneg q.totient))

/-- **Lambda-to-prime AP prefix-max bridge.**  This is the requested finite
partial-summation conclusion, connected literally to
`standardPrimeAPPrefixMaxError`.  It assumes no BV/AP prime-counting theorem. -/
theorem standardPrimeAPPrefixMaxError_le_lambda_bridge
    {N q : ℕ} (hq : 0 < q) :
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
      discreteAbelAmplifierPrefixMax N *
        (lambdaAPPrefixMaxError N q +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourcePrefixMaxError N := by
  unfold MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  unfold MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError
  dsimp only
  split_ifs with hS
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    exact abs_standardPrimeAPError_le_prefix_bridge hq hyN ha
  · exact bridgeRHS_nonneg N q

/-- Composition with the already-proved principal/nonprincipal character
majorant.  In particular the global/principal Chebyshev error remains visible
and is not silently charged to the nonprincipal characters. -/
theorem standardPrimeAPPrefixMaxError_le_principal_character_bridge
    {N q : ℕ} (hq : 0 < q) :
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
      discreteAbelAmplifierPrefixMax N *
        ((q.totient : ℝ)⁻¹ *
            (principalLambdaPrefixMaxError N q +
              ∑ χ ∈ nonprincipalCharacters q,
                lambdaCharacterPrefixMaxAmplitude N q χ) +
          lambdaPrimePowerCorrectionPrefixMaxError N q) +
      (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourcePrefixMaxError N := by
  refine (standardPrimeAPPrefixMaxError_le_lambda_bridge hq).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (discreteAbelAmplifierPrefixMax_nonneg N)
    exact add_le_add (lambdaAPPrefixMaxError_le_character_majorant hq) le_rfl
  · exact le_rfl

end

end AnalyticNumberTheory.LargeSieve
