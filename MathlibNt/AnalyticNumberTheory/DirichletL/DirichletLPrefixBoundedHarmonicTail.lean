import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticHarmonicTruncation
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradov

/-!
# Harmonic tails from a uniform character-prefix bound

This is the partial-summation bridge needed after Pólya--Vinogradov.  Unlike the
elementary period estimate, the loss is the supplied prefix amplitude `P`, not
the modulus.  No lower bound for `L(1, χ)` is asserted here.
-/

open Complex Finset Filter
open scoped Topology

namespace DirichletCharacter

open DirichletLWeakStripDerivative DirichletLAbelWeightVariation
  DirichletLConditionalValueSeries

variable {q : ℕ} [NeZero q]

private lemma norm_sum_Ico_cpowWeight_character_le_of_prefix_bound
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 < s.re)
    (P : ℝ) (hP : ∀ N : ℕ, ‖∑ k ∈ range N, χ k‖ ≤ P)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ‖∑ k ∈ Ico m n, cpowWeight s k * χ k‖ ≤
      P * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
  have hab := dirichlet_cpow_abel_Ico χ s hmn
  simp_rw [← cpowWeight_nat_eq] at hab
  rw [hab]
  calc
    _ ≤ ‖cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k)‖ +
          ‖cpowWeight s m * (∑ k ∈ range m, χ k)‖ +
          ‖∑ k ∈ Ico m (n - 1),
            (cpowWeight s (k + 1 : ℕ) - cpowWeight s k) *
              (∑ j ∈ range (k + 1), χ j)‖ := by
      calc
        _ ≤ ‖cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k) -
              cpowWeight s m * (∑ k ∈ range m, χ k)‖ +
              ‖∑ k ∈ Ico m (n - 1),
                (cpowWeight s (k + 1 : ℕ) - cpowWeight s k) *
                  (∑ j ∈ range (k + 1), χ j)‖ := norm_sub_le _ _
        _ ≤ _ := by
          have h := norm_sub_le
            (cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k))
            (cpowWeight s m * (∑ k ∈ range m, χ k))
          linarith
    _ ≤ ‖cpowWeight s (n - 1 : ℕ)‖ * P + ‖cpowWeight s m‖ * P +
          ∑ k ∈ Ico m (n - 1),
            (‖cpowWeight s (k + 1 : ℕ) - cpowWeight s k‖ * P) := by
      gcongr
      · rw [norm_mul]
        gcongr
        exact hP n
      · rw [norm_mul]
        gcongr
        exact hP m
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        gcongr
        exact hP (k + 1)
    _ = P * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          ∑ k ∈ Ico m (n - 1),
            ‖cpowWeight s (k + 1 : ℕ) - cpowWeight s k‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ P * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
      have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0)
      gcongr
      simpa only [Nat.pred_eq_sub_one, Nat.cast_add, Nat.cast_one] using
        sum_norm_cpowWeight_sub_le s hs hm (Nat.le_pred_of_lt hmn)

/-- General-`s` Abel tail with an arbitrary uniform prefix bound.  This is the
source-level bridge needed before specializing Pólya--Vinogradov in Chen 1973,
Lemma 3. -/
theorem norm_LFunction_sub_sum_le_of_prefix_bound
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    (P : ℝ) (hP : ∀ N : ℕ, ‖∑ k ∈ range N, χ k‖ ≤ P)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖χ.LFunction s - ∑ k ∈ range m, cpowWeight s k * χ k‖ ≤
      P * ((m : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
  let V := orderedValueSeries χ hχ s hs
  let S : ℕ → ℂ := fun n => ∑ k ∈ range n, cpowWeight s k * χ k
  have hS : Tendsto S atTop (𝓝 V) := by
    simpa only [S, V] using
      tendsto_sum_range_orderedValueSeries χ hχ s hs
  have hleft : Tendsto (fun n => ‖S (n + 1) - S m‖) atTop (𝓝 ‖V - S m‖) :=
    ((hS.comp (tendsto_add_atTop_nat 1)).sub_const (S m)).norm
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hwm : ‖cpowWeight s m‖ = (m : ℝ) ^ (-s.re) := by
    rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
    simp
  have hright : Tendsto
      (fun n : ℕ => P * (‖cpowWeight s n‖ + (m : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re))) atTop
      (𝓝 (P * ((m : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)))) := by
    simpa only [zero_add, add_assoc] using
      ((tendsto_norm_cpowWeight_nat_atTop s hs).add_const
        ((m : ℝ) ^ (-s.re) +
          (‖s‖ / s.re) * (m : ℝ) ^ (-s.re))).const_mul P
  have hlim : ‖V - S m‖ ≤ P * ((m : ℝ) ^ (-s.re) +
      (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
    refine le_of_tendsto_of_tendsto hleft hright ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn : m < n + 1 := Nat.lt_succ_of_le hn
    have ht := norm_sum_Ico_cpowWeight_character_le_of_prefix_bound
      χ s hs P hP hm hmn
    rw [Finset.sum_Ico_eq_sub _ hmn.le] at ht
    simpa only [S, Nat.add_sub_cancel, hwm] using ht
  dsimp only [V, S] at hlim
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ hχ s hs] at hlim
  exact hlim

/-- Partial summation improves the harmonic truncation tail from `2q/m` to
`2P/m` whenever every ordinary character prefix has norm at most `P`. -/
theorem norm_LFunction_one_sub_harmonic_sum_le_of_prefix_bound
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (P : ℝ)
    (hP : ∀ N : ℕ, ‖∑ k ∈ range N, χ k‖ ≤ P)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖χ.LFunction 1 - ∑ k ∈ range m, cpowWeight (1 : ℂ) k * χ k‖ ≤
      2 * P / (m : ℝ) := by
  calc
    _ ≤ P * ((m : ℝ)⁻¹ + (m : ℝ)⁻¹) := by
      simpa only [Complex.one_re, norm_one, div_one, one_mul, Real.rpow_neg_one] using
        norm_LFunction_sub_sum_le_of_prefix_bound χ hχ (1 : ℂ) (by norm_num) P hP hm
    _ = 2 * P / (m : ℝ) := by ring

/-- Real quadratic form of the prefix-bounded harmonic tail. -/
theorem abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le_of_prefix_bound
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (P : ℝ)
    (hP : ∀ N : ℕ, ‖∑ k ∈ range N, χ k‖ ≤ P)
    {m : ℕ} (hm : 1 ≤ m) :
    |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
      2 * P / (m : ℝ) := by
  have hnorm := norm_LFunction_one_sub_harmonic_sum_le_of_prefix_bound
    χ hχ P hP hm
  have hre := Complex.abs_re_le_norm
    (χ.LFunction 1 - ∑ k ∈ range m, cpowWeight (1 : ℂ) k * χ k)
  have hre' :
      |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
        ‖χ.LFunction 1 - ∑ k ∈ range m, cpowWeight (1 : ℂ) k * χ k‖ := by
    simpa [quadraticHarmonicTruncation] using hre
  exact hre'.trans hnorm

end DirichletCharacter