

import MathlibNt.AnalyticNumberTheory.LargeSieve.TruncatedPerronKernel
import MathlibNt.AnalyticNumberTheory.LargeSieve.RankOneRectangularPrimitiveL1

/-!
 # Finite rank-one separation of the damped arctangent kernel

This leaf contains only the finite algebra behind the later mean estimate.  It
splits the nonzero-frequency truncated Perron integrand into two rank-one
rectangular terms and records the coefficient-energy bounds needed to feed
`rankOneRectangularWeightedPrimitiveMean_le`.  It makes no final mean claim.

This module is intentionally not imported by a canonical facade.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The logarithm in the product kernel separates into its two rectangular
coordinates.  Positivity hypotheses are explicit because this is the form used
on positive integer rectangles. -/
theorem log_div_int_mul_eq_sub_log_sub_log
    {y : ℝ} {m n : ℤ} (hy : 0 < y) (hm : 0 < m) (hn : 0 < n) :
    Real.log (y / ((m * n : ℤ) : ℝ)) =
      (Real.log y - Real.log (m : ℝ)) - Real.log (n : ℝ) := by
  rw [Real.log_div hy.ne' (by positivity : (((m * n : ℤ) : ℝ) ≠ 0))]
  rw [show (((m * n : ℤ) : ℝ) = (m : ℝ) * (n : ℝ)) by norm_num]
  rw [Real.log_mul (by positivity : (m : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  ring

/-- Sine twist in the left rectangle. -/
def leftSinTwist (a : ℤ → ℂ) (y t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.sin (t * (Real.log y - Real.log (m : ℝ))) : ℂ)

/-- Cosine twist in the left rectangle. -/
def leftCosTwist (a : ℤ → ℂ) (y t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.cos (t * (Real.log y - Real.log (m : ℝ))) : ℂ)

/-- Sine twist in the right rectangle. -/
def rightSinTwist (b : ℤ → ℂ) (t : ℝ) (n : ℤ) : ℂ :=
  b n * (Real.sin (t * Real.log (n : ℝ)) : ℂ)

/-- Cosine twist in the right rectangle. -/
def rightCosTwist (b : ℤ → ℂ) (t : ℝ) (n : ℤ) : ℂ :=
  b n * (Real.cos (t * Real.log (n : ℝ)) : ℂ)

/-- Exact pointwise rank-one separation at a nonzero frequency.  The common
factor `1/t` is deliberately outside the four coefficient twists. -/
theorem truncatedPerronIntegrand_log_div_int_mul_eq_rankOne
    {y t : ℝ} {m n : ℤ} (hy : 0 < y) (hm : 0 < m) (hn : 0 < n) (ht : t ≠ 0) :
    (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ) =
      (1 / (t : ℂ)) *
        (((Real.sin (t * (Real.log y - Real.log (m : ℝ))) : ℂ) *
            (Real.cos (t * Real.log (n : ℝ)) : ℂ)) -
          ((Real.cos (t * (Real.log y - Real.log (m : ℝ))) : ℂ) *
            (Real.sin (t * Real.log (n : ℝ)) : ℂ))) := by
  rw [truncatedPerronIntegrand, if_neg ht]
  rw [log_div_int_mul_eq_sub_log_sub_log hy hm hn]
  rw [show t * ((Real.log y - Real.log (m : ℝ)) - Real.log (n : ℝ)) =
      t * (Real.log y - Real.log (m : ℝ)) - t * Real.log (n : ℝ) by ring]
  rw [Real.sin_sub]
  push_cast
  field_simp

/-- The original rectangular double sum with the truncated Perron integrand. -/
def rectangularKernelCharacterSum
    (a b : ℤ → ℂ) (y t : ℝ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)

/-- Four one-dimensional rectangular Dirichlet sums reproduce the original
kernel-weighted double sum exactly.  Its quantifier order and interval format
match `rankOneRectangularWeightedPrimitiveMean_le` directly. -/
theorem rectangularKernelCharacterSum_eq_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} (hy : 0 < y) (ht : t ≠ 0)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hm : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 0 < m)
    (hn : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < n) :
    rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ =
      (1 / (t : ℂ)) *
        ((∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
            leftSinTwist a y t m * χ.1 (m : ZMod q)) *
          (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
            rightCosTwist b t n * χ.1 (n : ZMod q)) -
         (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
            leftCosTwist a y t m * χ.1 (m : ZMod q)) *
          (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
            rightSinTwist b t n * χ.1 (n : ZMod q))) := by
  have hSC :
      (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
          leftSinTwist a y t m * χ.1 (m : ZMod q)) *
        (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          rightCosTwist b t n * χ.1 (n : ZMod q)) =
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          (leftSinTwist a y t m * χ.1 (m : ZMod q)) *
            (rightCosTwist b t n * χ.1 (n : ZMod q)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hmm
    rw [Finset.mul_sum]
  have hCS :
      (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
          leftCosTwist a y t m * χ.1 (m : ZMod q)) *
        (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          rightSinTwist b t n * χ.1 (n : ZMod q)) =
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          (leftCosTwist a y t m * χ.1 (m : ZMod q)) *
            (rightSinTwist b t n * χ.1 (n : ZMod q)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hmm
    rw [Finset.mul_sum]
  unfold rectangularKernelCharacterSum
  calc
    (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)) =
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          (1 / (t : ℂ)) *
            ((leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                (rightCosTwist b t n * χ.1 (n : ZMod q)) -
              (leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                (rightSinTwist b t n * χ.1 (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro m hmm
      apply Finset.sum_congr rfl
      intro n hnn
      rw [truncatedPerronIntegrand_log_div_int_mul_eq_rankOne
        hy (hm m hmm) (hn n hnn) ht]
      simp only [leftSinTwist, leftCosTwist, rightSinTwist, rightCosTwist]
      rw [Int.cast_mul, map_mul]
      push_cast
      ring
    _ = (1 / (t : ℂ)) *
        ((∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
            ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
              (leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                (rightCosTwist b t n * χ.1 (n : ZMod q))) -
          (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
            ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
              (leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                (rightSinTwist b t n * χ.1 (n : ZMod q)))) := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by rw [← hSC, ← hCS]

/-- A sine twist costs the square of `min 1 (L*|t|)` when the logarithmic
coordinate has absolute value at most `L`. -/
theorem sum_norm_sq_leftSinTwist_le
    (a : ℤ → ℂ) (y t L : ℝ) (s : Finset ℤ)
    (hL : 0 ≤ L) (hlog : ∀ m ∈ s, |Real.log y - Real.log (m : ℝ)| ≤ L) :
    ∑ m ∈ s, ‖leftSinTwist a y t m‖ ^ 2 ≤
      (min 1 (L * |t|)) ^ 2 * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  simp only [leftSinTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hs1 : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤ 1 :=
    Real.abs_sin_le_one _
  have hsL : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤ L * |t| := by
    calc
      |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤
          |t * (Real.log y - Real.log (m : ℝ))| := Real.abs_sin_le_abs
      _ = |t| * |Real.log y - Real.log (m : ℝ)| := abs_mul _ _
      _ ≤ |t| * L := mul_le_mul_of_nonneg_left (hlog m hm) (abs_nonneg t)
      _ = L * |t| := by ring
  have hs : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ≤ min 1 (L * |t|) :=
    le_min hs1 hsL
  have hmin : 0 ≤ min 1 (L * |t|) :=
    le_min (by norm_num) (mul_nonneg hL (abs_nonneg t))
  have hs2 : |Real.sin (t * (Real.log y - Real.log (m : ℝ)))| ^ 2 ≤
      min 1 (L * |t|) ^ 2 := (sq_le_sq₀ (abs_nonneg _) hmin).2 hs
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hs2 (sq_nonneg ‖a m‖)

/-- Nonnegative-frequency form with the literal damping factor `min 1 (L*t)`. -/
theorem sum_norm_sq_leftSinTwist_le_of_nonneg
    (a : ℤ → ℂ) (y t L : ℝ) (s : Finset ℤ)
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hlog : ∀ m ∈ s, |Real.log y - Real.log (m : ℝ)| ≤ L) :
    ∑ m ∈ s, ‖leftSinTwist a y t m‖ ^ 2 ≤
      (min 1 (L * t)) ^ 2 * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  simpa [abs_of_nonneg ht] using sum_norm_sq_leftSinTwist_le a y t L s hL hlog

/-- A cosine twist never enlarges coefficient energy. -/
theorem sum_norm_sq_leftCosTwist_le
    (a : ℤ → ℂ) (y t : ℝ) (s : Finset ℤ) :
    ∑ m ∈ s, ‖leftCosTwist a y t m‖ ^ 2 ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro m hm
  simp only [leftCosTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hc := Real.abs_cos_le_one (t * (Real.log y - Real.log (m : ℝ)))
  have hc2 : |Real.cos (t * (Real.log y - Real.log (m : ℝ)))| ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (Real.cos (t * (Real.log y - Real.log (m : ℝ))))]
  simpa using mul_le_mul_of_nonneg_left hc2 (sq_nonneg ‖a m‖)

/-- Right sine energy bound. -/
theorem sum_norm_sq_rightSinTwist_le
    (b : ℤ → ℂ) (t L : ℝ) (s : Finset ℤ)
    (hL : 0 ≤ L) (hlog : ∀ n ∈ s, |Real.log (n : ℝ)| ≤ L) :
    ∑ n ∈ s, ‖rightSinTwist b t n‖ ^ 2 ≤
      (min 1 (L * |t|)) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  simp only [rightSinTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hs1 : |Real.sin (t * Real.log (n : ℝ))| ≤ 1 := Real.abs_sin_le_one _
  have hsL : |Real.sin (t * Real.log (n : ℝ))| ≤ L * |t| := by
    calc
      |Real.sin (t * Real.log (n : ℝ))| ≤ |t * Real.log (n : ℝ)| :=
        Real.abs_sin_le_abs
      _ = |t| * |Real.log (n : ℝ)| := abs_mul _ _
      _ ≤ |t| * L := mul_le_mul_of_nonneg_left (hlog n hn) (abs_nonneg t)
      _ = L * |t| := by ring
  have hs : |Real.sin (t * Real.log (n : ℝ))| ≤ min 1 (L * |t|) := le_min hs1 hsL
  have hmin : 0 ≤ min 1 (L * |t|) :=
    le_min (by norm_num) (mul_nonneg hL (abs_nonneg t))
  have hs2 : |Real.sin (t * Real.log (n : ℝ))| ^ 2 ≤ min 1 (L * |t|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hmin).2 hs
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hs2 (sq_nonneg ‖b n‖)

/-- Nonnegative-frequency right sine-energy form. -/
theorem sum_norm_sq_rightSinTwist_le_of_nonneg
    (b : ℤ → ℂ) (t L : ℝ) (s : Finset ℤ)
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hlog : ∀ n ∈ s, |Real.log (n : ℝ)| ≤ L) :
    ∑ n ∈ s, ‖rightSinTwist b t n‖ ^ 2 ≤
      (min 1 (L * t)) ^ 2 * ∑ n ∈ s, ‖b n‖ ^ 2 := by
  simpa [abs_of_nonneg ht] using sum_norm_sq_rightSinTwist_le b t L s hL hlog

/-- Right cosine energy bound. -/
theorem sum_norm_sq_rightCosTwist_le
    (b : ℤ → ℂ) (t : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, ‖rightCosTwist b t n‖ ^ 2 ≤ ∑ n ∈ s, ‖b n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  simp only [rightCosTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hc := Real.abs_cos_le_one (t * Real.log (n : ℝ))
  have hc2 : |Real.cos (t * Real.log (n : ℝ))| ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (Real.cos (t * Real.log (n : ℝ)))]
  simpa using mul_le_mul_of_nonneg_left hc2 (sq_nonneg ‖b n‖)

/-- On positive integer support `n ≤ M`, the right logarithmic coordinate is
bounded by `log M`. -/
theorem abs_log_int_le_log
    {M : ℕ} (_hM : 1 ≤ M) {n : ℤ} (hn1 : 1 ≤ n) (hnM : n ≤ (M : ℤ)) :
    |Real.log (n : ℝ)| ≤ Real.log (M : ℝ) := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnMreal : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
  rw [abs_of_nonneg (Real.log_nonneg hnreal)]
  exact Real.log_le_log (by positivity) hnMreal

/-- Half-step geometry bound for the left logarithmic coordinate.  The lower
half-step hypothesis is necessary: an upper bound on `y` alone cannot control
`|log y|`. -/
theorem abs_log_div_int_le_two_log
    {M : ℕ} (hM : 3 ≤ M) {y : ℝ} (hy0 : 1 / 2 ≤ y)
    (hyM : y ≤ (M : ℝ) + 1 / 2) {m : ℤ} (hm1 : 1 ≤ m) (hmM : m ≤ (M : ℤ)) :
    |Real.log y - Real.log (m : ℝ)| ≤ 2 * Real.log (M : ℝ) := by
  have hMr : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : 0 < (M : ℝ) := lt_of_lt_of_le (by norm_num) hMr

  have hmreal1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmrealM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hmrealpos : 0 < (m : ℝ) := lt_of_lt_of_le (by norm_num) hmreal1
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy0
  have hloRatio : 1 / (M : ℝ) ^ 2 ≤ y / (m : ℝ) := by
    apply (le_div_iff₀ hmrealpos).2
    have hmHalf : (m : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hMrpos)).2
      nlinarith [hmrealM]
    calc
      (1 / (M : ℝ) ^ 2) * (m : ℝ) = (m : ℝ) / (M : ℝ) ^ 2 := by ring
      _ ≤ 1 / 2 := hmHalf
      _ ≤ y := hy0
  have hhiRatio : y / (m : ℝ) ≤ (M : ℝ) ^ 2 := by
    apply (div_le_iff₀ hmrealpos).2
    have hMsq : (M : ℝ) + 1 / 2 ≤ (M : ℝ) ^ 2 := by nlinarith
    have hySq : y ≤ (M : ℝ) ^ 2 := hyM.trans hMsq
    calc
      y ≤ (M : ℝ) ^ 2 := hySq
      _ = (M : ℝ) ^ 2 * 1 := by ring
      _ ≤ (M : ℝ) ^ 2 * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hmreal1 (sq_nonneg (M : ℝ))
  have hlogLo : -2 * Real.log (M : ℝ) ≤ Real.log (y / (m : ℝ)) := by
    have h := Real.log_le_log (by positivity : 0 < 1 / (M : ℝ) ^ 2) hloRatio
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
      Real.log_pow] at h
    simpa [two_mul] using h
  have hlogHi : Real.log (y / (m : ℝ)) ≤ 2 * Real.log (M : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < y / (m : ℝ)) hhiRatio
    rw [Real.log_pow] at h
    simpa [two_mul] using h
  rw [← Real.log_div hypos.ne' hmrealpos.ne']
  exact (abs_le).2 ⟨by simpa only [neg_mul] using hlogLo, hlogHi⟩

/-- Half-step specialization of the left sine-energy estimate on a rectangle.
This is in exactly the `Icc (start+1) (start+length)` format consumed by the
rank-one primitive mean theorem. -/
theorem sum_norm_sq_leftSinTwist_Icc_le_of_halfstep
    (a : ℤ → ℂ) (y t : ℝ) (Ma : ℤ) (Na M : ℕ)
    (hM : 3 ≤ M) (hy0 : 1 / 2 ≤ y) (hyM : y ≤ (M : ℝ) + 1 / 2)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ)) :
    ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖leftSinTwist a y t m‖ ^ 2 ≤
      (min 1 ((2 * Real.log (M : ℝ)) * |t|)) ^ 2 *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2 := by
  apply sum_norm_sq_leftSinTwist_le
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hM)))
  · intro m hm
    exact abs_log_div_int_le_two_log hM hy0 hyM (hm1 m hm) (hmM m hm)

/-- Positive-support specialization of the right sine-energy estimate on the
same rectangle format. -/
theorem sum_norm_sq_rightSinTwist_Icc_le
    (b : ℤ → ℂ) (t : ℝ) (Mb : ℤ) (Nb M : ℕ)
    (hM : 1 ≤ M)
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖rightSinTwist b t n‖ ^ 2 ≤
      (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2 := by
  apply sum_norm_sq_rightSinTwist_le
  · exact Real.log_nonneg (by exact_mod_cast hM)
  · intro n hn
    exact abs_log_int_le_log hM (hn1 n hn) (hnM n hn)

end

end AnalyticNumberTheory.LargeSieve
