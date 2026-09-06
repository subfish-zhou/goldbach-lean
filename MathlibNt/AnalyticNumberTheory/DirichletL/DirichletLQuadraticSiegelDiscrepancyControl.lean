import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelConvolution

/-!
# Explicit floor-sum control of the quadratic Siegel convolution discrepancy

This file opens the divisor double sum and records the exact floor-sum form.
The cutoff error is then separated into a short floor error and a genuinely
oscillatory long tail.  In particular, the floor error costs only the cutoff
`m`, rather than the ambient length `X`.
-/

open Complex Finset
open DirichletLAbelWeightVariation
open scoped BigOperators

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- Finite Abel summation with a nonnegative decreasing weight.  This is the
form used below for `w(d)=⌊X/d⌋`; only interval-prefix cancellation is paid. -/
lemma abs_sum_range_mul_le_of_prefix
    (f w : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hpref : ∀ k ≤ n, |∑ i ∈ range k, f i| ≤ B)
    (hw0 : ∀ i, 0 ≤ w i)
    (hwmono : ∀ i, i + 1 < n → w (i + 1) ≤ w i) :
    |∑ i ∈ range n, w i * f i| ≤ B * w 0 := by
  cases n with
  | zero => simpa using mul_nonneg hB (hw0 0)
  | succ k =>
      rw [show (∑ i ∈ range (k + 1), w i * f i) =
          ∑ i ∈ range (k + 1), w i • f i by simp]
      rw [Finset.sum_range_by_parts]
      simp only [Nat.add_sub_cancel, smul_eq_mul]
      calc
        |w k * (∑ i ∈ range (k + 1), f i) -
            ∑ i ∈ range k, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), f j| ≤
            |w k * (∑ i ∈ range (k + 1), f i)| +
              |∑ i ∈ range k, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), f j| :=
          abs_sub _ _
        _ ≤ B * w k +
            ∑ i ∈ range k, B * (w i - w (i + 1)) := by
          gcongr
          · rw [abs_mul, abs_of_nonneg (hw0 k)]
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left (hpref (k + 1) (by omega)) (hw0 k)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            apply sum_le_sum
            intro i hi
            rw [mem_range] at hi
            have hmono := hwmono i (by omega)
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left (hpref (i + 1) (by omega))
                (sub_nonneg.mpr hmono)
        _ = B * w 0 := by
          rw [← Finset.mul_sum, Finset.sum_range_sub']
          ring

 omit [NeZero q] in
/-- Reindex the divisor double sum by the divisor.  The multiplicity of `d` is
exactly `⌊X/d⌋`. -/
theorem quadraticDivisorDoubleSum_eq_floorSum
    (χ : DirichletCharacter ℂ q) (X : ℕ) :
    (∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re) =
      ∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ) * (χ d).re := by
  classical
  calc
    (∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, (χ d).re) =
        ∑ n ∈ Icc 1 X, ∑ d ∈ Icc 1 X, if d ∣ n then (χ d).re else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      rw [← sum_filter]
      apply sum_congr
      · ext d
        simp only [Nat.mem_divisors, mem_filter, mem_Icc]
        constructor
        · rintro ⟨hdn, hn0⟩
          exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hdn, hn0⟩),
            (Nat.le_of_dvd hn.1 hdn).trans hn.2⟩, hdn⟩
        · rintro ⟨⟨hd1, hdX⟩, hdn⟩
          exact ⟨hdn, by omega⟩
      · intro d hd
        simp only [mem_filter] at hd
        simp []
    _ = ∑ d ∈ Icc 1 X, ∑ n ∈ Icc 1 X, if d ∣ n then (χ d).re else 0 := by
      rw [sum_comm]
    _ = ∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ) * (χ d).re := by
      apply sum_congr rfl
      intro d hd
      rw [mem_Icc] at hd
      rw [← sum_filter]
      have hcard : ((Icc 1 X).filter fun n => d ∣ n).card = X / d := by
        rw [← Nat.card_multiples' X d]
        congr 1
        ext n
        constructor
        · simp only [mem_filter, mem_Icc]
          rintro ⟨⟨hn1, hnX⟩, hdn⟩
          simp only [mem_range]
          exact ⟨Nat.lt_succ_of_le hnX, by omega, hdn⟩
        · simp only [mem_filter, mem_range]
          rintro ⟨hnX, hn0, hdn⟩
          simp only [mem_Icc]
          exact ⟨⟨Nat.pos_of_ne_zero hn0, Nat.le_of_lt_succ hnX⟩, hdn⟩
      simp [hcard]

omit [NeZero q] in
/-- At `s=1`, the real harmonic truncation is the ordinary finite sum
`∑_{1≤d<m} Re χ(d)/d`. -/
theorem quadraticHarmonicTruncation_eq_Ico
    (χ : DirichletCharacter ℂ q) (m : ℕ) :
    quadraticHarmonicTruncation χ m =
      ∑ d ∈ Ico 1 m, (χ d).re / (d : ℝ) := by
  classical
  unfold quadraticHarmonicTruncation
  rw [Complex.re_sum]
  have hsub : Ico 1 m ⊆ range m := by
    intro d hd
    exact mem_range.mpr (mem_Ico.mp hd).2
  rw [← Finset.sum_subset hsub]
  · apply sum_congr rfl
    intro d hd
    rw [mem_Ico] at hd
    have hdpos : 0 < d := by omega
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    simp [cpowWeight, Complex.cpow_neg_one, div_eq_mul_inv]
    field_simp [hd0]
  · intro d hdRange hdIco
    rw [mem_range] at hdRange
    have hd0 : d = 0 := by
      simp only [mem_Ico, not_and_or, not_le] at hdIco
      omega
    subst d
    simp [cpowWeight]

/-- Pólya--Vinogradov controls every real character interval, not merely prefixes. -/
theorem IsPrimitive.abs_sum_Ico_character_re_le_eight_mul_sqrt_q_mul_one_add_log
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 1 < q)
    (a b : ℕ) :
    |∑ n ∈ Ico a b, (χ n).re| ≤ 8 * Real.sqrt q * (1 + Real.log q) := by
  by_cases hab : a ≤ b
  · rw [← Complex.re_sum]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [Finset.sum_Ico_eq_sub (f := fun n => χ n) hab]
    calc
      ‖(∑ n ∈ range b, χ n) - ∑ n ∈ range a, χ n‖ ≤
          ‖∑ n ∈ range b, χ n‖ + ‖∑ n ∈ range a, χ n‖ := norm_sub_le _ _
      _ ≤ 4 * Real.sqrt q * (1 + Real.log q) +
          4 * Real.sqrt q * (1 + Real.log q) := by
        gcongr
        · simpa using hχ.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq b
        · simpa using hχ.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq a
      _ = 8 * Real.sqrt q * (1 + Real.log q) := by ring
  · rw [Finset.Ico_eq_empty (by omega)]
    simp
    positivity

/-- The long floor-weighted tail is controlled by interval prefixes through
finite Abel summation.  This is the cancellation step which prevents a
termwise `O(X)` bound. -/
theorem IsPrimitive.abs_floorWeighted_character_tail_le
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 1 < q)
    {m X : ℕ} (hm : 1 ≤ m) (_hmX : m ≤ X) :
    |∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re| ≤
      (8 * Real.sqrt q * (1 + Real.log q)) * ((X / m : ℕ) : ℝ) := by
  let L := X + 1 - m
  let f : ℕ → ℝ := fun i => (χ (m + i)).re
  let w : ℕ → ℝ := fun i => ((X / (m + i) : ℕ) : ℝ)
  have hset : Icc m X = Ico m (X + 1) := by
    ext d
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hB : 0 ≤ 8 * Real.sqrt q * (1 + Real.log q) := by
    have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hq)
    positivity
  have hab := abs_sum_range_mul_le_of_prefix f w L
    (8 * Real.sqrt q * (1 + Real.log q)) hB (by
      intro k hk
      rw [show (∑ i ∈ range k, f i) = ∑ n ∈ Ico m (m + k), (χ n).re by
        simpa [f] using
          (Finset.sum_Ico_eq_sum_range (fun n => (χ n).re) m (m + k)).symm]
      exact hχ.abs_sum_Ico_character_re_le_eight_mul_sqrt_q_mul_one_add_log
        hq m (m + k)) (by
      intro i
      dsimp only [w]
      exact_mod_cast Nat.zero_le (X / (m + i))) (by
      intro i hi
      dsimp only [w]
      exact_mod_cast Nat.div_le_div_left (Nat.le_succ (m + i))
        (by omega : 0 < m + i))
  simpa only [L, f, w, Nat.cast_add, Nat.add_zero, zero_add] using hab

omit [NeZero q] in
/-- Exact floor-sum expansion of the production discrepancy. -/
theorem quadraticSiegelConvolutionDiscrepancy_eq_floorSum_sub
    (χ : DirichletCharacter ℂ q) (X m : ℕ) :
    quadraticSiegelConvolutionDiscrepancy χ X m =
      (∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ) * (χ d).re) -
        (X : ℝ) * ∑ d ∈ Ico 1 m, (χ d).re / (d : ℝ) := by
  rw [quadraticSiegelConvolutionDiscrepancy,
    quadraticSiegelConvolutionSummatory_eq_divisorDoubleSum,
    quadraticDivisorDoubleSum_eq_floorSum,
    quadraticHarmonicTruncation_eq_Ico]

end DirichletCharacter