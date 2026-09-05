import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivativeBound

/-!
# A genuine weak-strip bound for nonprincipal Dirichlet L-values

The naturally ordered conditional value series is split at
`m = ⌊|t|⌋₊ + 1`.  Its finite prefix is bounded term by term and its explicit
Abel tail is absorbed into one fixed logarithmic bound.
-/

open Complex Finset Set

namespace DirichletLWeakStripValueBound

open DirichletLAbelWeightVariation
open DirichletLConditionalValueSeries
open DirichletLWeakStripDerivativeBound

variable {q : ℕ} [NeZero q]

/-- The finite value truncation costs only one logarithm in the weak strip. -/
lemma norm_value_truncation_le
    (χ : DirichletCharacter ℂ q) {A σ t : ℝ}
    (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hσ : 1 - A / Real.log |t| ≤ σ) (ht : 3 < |t|) :
    let m := ⌊|t|⌋₊ + 1
    ‖∑ n ∈ range m, cpowWeight (σ + t * I) n * χ n‖ ≤
      Real.exp A * 2 * Real.log |t| := by
  dsimp only
  let N := ⌊|t|⌋₊
  have haux := UpperBnd_aux hA ht hσ
  obtain ⟨hNpos, hNle, _, _, hσpos, _⟩ := haux
  have hlogt : 1 < Real.log |t| := logt_gt_one ht.le
  have hterm (n : ℕ) (hn : n ≤ N) :
      ‖cpowWeight (σ + t * I) n * χ n‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
    calc
      ‖cpowWeight (σ + t * I) n * χ n‖ =
          ‖cpowWeight (σ + t * I) n‖ * ‖χ n‖ := norm_mul _ _
      _ ≤ ‖cpowWeight (σ + t * I) n‖ * 1 :=
        mul_le_mul_of_nonneg_left (χ.norm_le_one n) (norm_nonneg _)
      _ = ‖(n : ℂ) ^ (-(σ + t * I))‖ := by
        rw [mul_one, cpowWeight_nat_eq]
      _ ≤ (n : ℝ)⁻¹ * Real.exp A := by
        apply ZetaBnd_aux2 hA.1 hσpos
        · linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
        · exact hσ
  have hsum := norm_sum_le_of_le (range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hterm)
  change ‖∑ n ∈ range (N + 1), cpowWeight (σ + t * I) n * χ n‖ ≤ _
  calc
    _ ≤ ∑ n ∈ range (N + 1), (n : ℝ)⁻¹ * Real.exp A := hsum
    _ = (∑ n ∈ range (N + 1), (n : ℝ)⁻¹) * Real.exp A := by
      rw [sum_mul]
    _ ≤ (1 + Real.log N) * Real.exp A := by
      gcongr
      rw [range_eq_Ico, ← Icc_eq_Ico, harmonic_eq_sum_Icc0]
      exact harmonic_le_one_add_log (n := N)
    _ ≤ (2 * Real.log |t|) * Real.exp A := by
      gcongr
      have hlogN : Real.log N ≤ Real.log |t| :=
        Real.log_le_log (by positivity) hNle
      linarith
    _ = Real.exp A * 2 * Real.log |t| := by ring

/-- At the canonical cutoff the explicit Abel tail is bounded by a fixed
multiple of `exp A * q * log |t|`. -/
lemma canonical_value_tail_le_fixed_log
    {A σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hσ : 1 - A / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2) (ht : 3 < |t|) :
    let m := ⌊|t|⌋₊ + 1
    q * ((m : ℝ) ^ (-σ) +
      (‖(σ + t * I : ℂ)‖ / σ) * (m : ℝ) ^ (-σ)) ≤
        Real.exp A * (50 * q) * Real.log |t| := by
  let m : ℕ := ⌊|t|⌋₊ + 1
  let P : ℝ := (m : ℝ) ^ (1 - σ)
  let L : ℝ := Real.log |t|
  have hσhalf : 1 / 2 < σ := one_half_lt_sigma hA ht hσ
  have hσpos : 0 < σ := by linarith
  have hmone : (1 : ℝ) ≤ m := by simp [m]
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmone
  have hP0 : 0 ≤ P := by positivity
  have hP : P ≤ 3 * Real.exp A := by
    simpa only [m, P] using natFloor_add_one_rpow_one_sub_sigma_le hA ht hσ
  have hL : 1 < L := by simpa only [L] using logt_gt_one ht.le
  have hinv : 1 / σ ≤ 2 := by
    rw [div_le_iff₀ hσpos]
    nlinarith
  have habsm : |t| < (m : ℝ) := by
    exact_mod_cast (abs_lt_natFloor_add_one (t := t))
  have hnorm : ‖(σ + t * I : ℂ)‖ ≤ 3 * (m : ℝ) := by
    have h := norm_sigma_add_tI_le_abs_add_two hA ht hσ hσ2
    linarith
  have hmneg0 : 0 ≤ (m : ℝ) ^ (-σ) := by positivity
  have hmnegP : (m : ℝ) ^ (-σ) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hmone (by linarith)
  have hm_mul_neg : (m : ℝ) * (m : ℝ) ^ (-σ) = P := by
    dsimp only [P]
    rw [show 1 - σ = 1 + (-σ) by ring, Real.rpow_add hmpos, Real.rpow_one]
  have hnormneg : ‖(σ + t * I : ℂ)‖ * (m : ℝ) ^ (-σ) ≤ 3 * P := by
    calc
      _ ≤ (3 * (m : ℝ)) * (m : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right hnorm hmneg0
      _ = 3 * P := by rw [← hm_mul_neg]; ring
  dsimp only
  change (q : ℝ) * ((m : ℝ) ^ (-σ) +
    (‖(σ + t * I : ℂ)‖ / σ) * (m : ℝ) ^ (-σ)) ≤ _
  calc
    _ = (q : ℝ) * ((m : ℝ) ^ (-σ) +
        (‖(σ + t * I : ℂ)‖ * (m : ℝ) ^ (-σ)) * (1 / σ)) := by ring
    _ ≤ (q : ℝ) * (P + (3 * P) * 2) := by gcongr
    _ ≤ (q : ℝ) * ((3 * Real.exp A) + (3 * (3 * Real.exp A)) * 2) := by
      gcongr
    _ = (q : ℝ) * (21 * Real.exp A) := by ring
    _ ≤ (q : ℝ) * (50 * Real.exp A * L) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      calc
        21 * Real.exp A ≤ 50 * Real.exp A :=
          mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos A).le
        _ = (50 * Real.exp A) * 1 := by ring
        _ ≤ (50 * Real.exp A) * L :=
          mul_le_mul_of_nonneg_left hL.le (by positivity)
        _ = 50 * Real.exp A * L := rfl
    _ = Real.exp A * (50 * q) * L := by ring

/-- Fully explicit weak-strip value bound for a nonprincipal character. -/
theorem norm_LFunction_le_fixed_log
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hσ : 1 - A / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2)
    (ht : 3 < |t|) :
    ‖χ.LFunction (σ + t * I)‖ ≤
      Real.exp A * (100 * q) * Real.log |t| := by
  let m : ℕ := ⌊|t|⌋₊ + 1
  have hσpos : 0 < σ := lt_trans (by norm_num) (one_half_lt_sigma hA ht hσ)
  have hsre : 0 < (σ + t * I : ℂ).re := by simpa using hσpos
  have hm : 1 ≤ m := by simp [m]
  have hseries := orderedValueSeries_eq_LFunction_of_re_pos
    χ hχ (σ + t * I) hsre
  have htail := norm_orderedValueSeries_sub_sum_range_le
    χ hχ (σ + t * I) hsre hm
  have hfinite := norm_value_truncation_le χ hA hσ ht
  have htail' := canonical_value_tail_le_fixed_log (q := q) hA hσ hσ2 ht
  dsimp only at hfinite htail'
  have htailBound :
      ‖orderedValueSeries χ hχ (σ + t * I) hsre -
        ∑ n ∈ range m, cpowWeight (σ + t * I) n * χ n‖ ≤
          Real.exp A * (50 * q) * Real.log |t| := by
    refine htail.trans ?_
    simpa only [m, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, mul_one, sub_self, add_zero] using htail'
  rw [← hseries]
  calc
    ‖orderedValueSeries χ hχ (σ + t * I) hsre‖ =
        ‖(∑ n ∈ range m, cpowWeight (σ + t * I) n * χ n) +
          (orderedValueSeries χ hχ (σ + t * I) hsre -
            ∑ n ∈ range m, cpowWeight (σ + t * I) n * χ n)‖ := by
              congr 1
              abel
    _ ≤ ‖∑ n ∈ range m, cpowWeight (σ + t * I) n * χ n‖ +
          ‖orderedValueSeries χ hχ (σ + t * I) hsre -
            ∑ n ∈ range m, cpowWeight (σ + t * I) n * χ n‖ := norm_add_le _ _
    _ ≤ Real.exp A * 2 * Real.log |t| +
          Real.exp A * (50 * q) * Real.log |t| :=
      add_le_add hfinite htailBound
    _ = Real.exp A * (2 + 50 * q) * Real.log |t| := by ring
    _ ≤ Real.exp A * (100 * q) * Real.log |t| := by
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      have hlog : 0 ≤ Real.log |t| := by linarith [logt_gt_one ht.le]
      apply mul_le_mul_of_nonneg_right _ hlog
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos A).le
      nlinarith

/-! ## The principal-character lane -/

/-- A bad Euler factor is bounded by its underlying prime throughout the
closed right half-plane.  The nonnegative-real-part version is useful because
the zeta zero-free strip extends slightly to the left of `re s = 1`. -/
lemma principalEulerFactorNorm_le_prime
    {s : ℂ} (hs : 0 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ p := by
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
    calc
      ‖(p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (0 : ℂ)‖ := by
        apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hp.pos
        simp only [neg_re, zero_re]
        linarith
      _ = 1 := by simp
  calc
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by simpa using add_le_add_left hpow 1
    _ ≤ p := by exact_mod_cast hp.two_le

/-- The finite Euler correction for the principal character costs at most its
modulus.  This stronger nonnegative-real-part form covers the zeta strip. -/
lemma principalEulerCorrectionNorm_le_modulus_of_nonneg_re
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ q := by
  calc
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ =
        ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ := by simp
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := by
      gcongr with p hp
      exact principalEulerFactorNorm_le_prime hs (Nat.prime_of_mem_primeFactors hp)
    _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by simp
    _ ≤ q := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

/-- Requested `re s ≥ 1` specialization of the Euler-correction bound. -/
lemma principalEulerCorrectionNorm_le_modulus
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ q :=
  principalEulerCorrectionNorm_le_modulus_of_nonneg_re q (by linarith)

/-- Uniform weak-strip logarithmic bound for the principal Dirichlet
`L`-function.  The zeta constants are selected before the modulus. -/
theorem exists_principal_norm_LFunctionTrivChar_le_log :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C),
      ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 3 < |t| →
        σ ∈ Set.Icc (1 - A / Real.log |t|) 2 →
        ‖DirichletCharacter.LFunctionTrivChar q (σ + t * I)‖ ≤
          C * q * Real.log |t| := by
  rcases ZetaUpperBnd with ⟨A, hA, C, hC, hzeta⟩
  refine ⟨A, hA, C, hC, ?_⟩
  intro q _ σ t ht hσ
  have hσpos : 0 < σ := by
    have hlog : 1 < Real.log |t| := logt_gt_one ht.le
    have hratio : A / Real.log |t| < 1 / 2 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [hA.2]
    linarith [hσ.1]
  have hsne : (σ + t * I : ℂ) ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    have ht0 : t ≠ 0 := by
      intro h
      subst t
      norm_num at ht
    norm_num at him
    exact ht0 him
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne, norm_mul]
  calc
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(σ + t * I)))‖ *
        ‖riemannZeta (σ + t * I)‖ ≤ (q : ℝ) * (C * Real.log |t|) := by
      gcongr
      · apply principalEulerCorrectionNorm_le_modulus_of_nonneg_re q
        norm_num
        exact hσpos.le
      · exact hzeta σ t ht hσ
    _ = C * q * Real.log |t| := by ring

end DirichletLWeakStripValueBound
