import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdMean

/-!
# A common-index and r mean in the main nonzero branch

Fouvry (1987), p. 632, (4.8). The constant term, not the slope, is
nonzero when `h'*s ≠ h*s'`. The r mean removes the whole r gcd cost.
The subsequent common-index mean uses that constant term. The remaining
`s*s'` gcd and divisor weight are retained explicitly, not bounded by a
power of the scale and silently absorbed into an epsilon loss.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def iv3MainConstant (n₂ n₂' s s' : ℕ) (a h h' : ℤ) : ℤ :=
  a * n₂ * n₂' * (h' * s - h * s')

theorem iv3CorrelationNumerator_affine (d₁ n n₂ n₂' s s' : ℕ) (a h h' : ℤ) :
    iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' =
      iv3MainConstant n₂ n₂' s s' a h h' +
        (a * d₁ * (h * n₂' * s' - h' * n₂ * s)) * n := by
  unfold iv3CorrelationNumerator iv3MainConstant
  ring

theorem iv3MainConstant_ne_zero
    {n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (ha : a ≠ 0) (hn₂ : 0 < n₂) (hn₂' : 0 < n₂')
    (hmain : h' * s ≠ h * s') :
    iv3MainConstant n₂ n₂' s s' a h h' ≠ 0 := by
  unfold iv3MainConstant
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha (by exact_mod_cast hn₂.ne'))
    (by exact_mod_cast hn₂'.ne')) (sub_ne_zero.mpr hmain)

theorem iv3_main_index_gcd (d₁ n n₂ n₂' s s' : ℕ) (a h h' : ℤ) :
    n.gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs =
      n.gcd (iv3MainConstant n₂ n₂' s s' a h h').natAbs := by
  have he := Int.gcd_add_mul_right_right (n : ℤ)
    (iv3MainConstant n₂ n₂' s s' a h h')
    (a * d₁ * (h * n₂' * s' - h' * n₂ * s))
  rw [← iv3CorrelationNumerator_affine] at he
  simpa only [Int.gcd, Int.natAbs_natCast] using he

private theorem main_gcd_mul_le (u v : ℕ) {A : ℕ} (hA : 0 < A) :
    (u * v).gcd A ≤ u.gcd A * v.gcd A :=
by
  simpa only [Nat.mul_comm] using gcd_mul_le_gcd_mul_gcd hA u v

/-- The complete modulus gcd is separated without a loss of `r`, `s`,
or `s'`. No coprimality assumptions are needed for this inequality. -/
theorem iv3_main_gcd_le
    {d₁ n n₂ n₂' r s s' : ℕ} {a h h' : ℤ}
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) :
    (n * r * s * s').gcd
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs ≤
      n.gcd (iv3MainConstant n₂ n₂' s s' a h h').natAbs *
        (s * s').gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs *
        r.gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs := by
  have hA := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hl)
  calc
    _ = (n * (s * s') * r).gcd
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs := by congr 1; ring
    _ ≤ ((n * (s * s')).gcd
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) *
        r.gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs :=
      main_gcd_mul_le _ _ hA
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      simpa only [iv3_main_index_gcd] using main_gcd_mul_le n (s * s') hA

theorem iv3_main_gcd_r_sum
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) (R : ℕ) :
    (∑ r ∈ Ioc 0 R, (n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) ≤
      R * (n.gcd (iv3MainConstant n₂ n₂' s s' a h h').natAbs *
        (s * s').gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs *
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs.divisors.card) := by
  calc
    _ ≤ ∑ r ∈ Ioc 0 R,
        (n.gcd (iv3MainConstant n₂ n₂' s s' a h h').natAbs *
          (s * s').gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) *
        r.gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs :=
      sum_le_sum (fun _ _ => iv3_main_gcd_le hl)
    _ = _ * ∑ r ∈ Ioc 0 R,
        r.gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs :=
      (mul_sum _ _ _).symm
    _ ≤ _ * (R *
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs.divisors.card) := by
      apply Nat.mul_le_mul_left
      simpa only [Nat.gcd_comm] using sum_gcd_le (Int.natAbs_ne_zero.mpr hl) R
    _ = _ := by ring

theorem iv3_main_sqrt_gcd_r_sum
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) (R : ℕ) :
    (∑ r ∈ Ioc 0 R, Real.sqrt ((n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      R * (Real.sqrt (n.gcd (iv3MainConstant n₂ n₂' s s' a h h').natAbs : ℝ) *
        Real.sqrt (((s * s').gcd
          (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs *
          (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs.divisors.card : ℕ) : ℝ)) := by
  let B := (iv3MainConstant n₂ n₂' s s' a h h').natAbs
  let A := (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs
  have hm : (∑ r ∈ Ioc 0 R, ((n * r * s * s').gcd A : ℝ)) ≤
      (R * (n.gcd B * (s * s').gcd A * A.divisors.card) : ℕ) := by
    exact_mod_cast iv3_main_gcd_r_sum hl R
  calc
    _ ≤ Real.sqrt (R : ℝ) *
        Real.sqrt (∑ r ∈ Ioc 0 R, ((n * r * s * s').gcd A : ℝ)) := by
      simpa using Real.sum_sqrt_mul_sqrt_le (f := fun _ : ℕ => (1 : ℝ))
        (g := fun r => ((n * r * s * s').gcd A : ℝ))
        (Ioc 0 R) (fun _ => by positivity) (fun _ => by positivity)
    _ ≤ Real.sqrt (R : ℝ) *
        Real.sqrt ((R * (n.gcd B * (s * s').gcd A * A.divisors.card) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg R)]
      have he : (R : ℝ) * ((R * (n.gcd B * (s * s').gcd A *
          A.divisors.card) : ℕ) : ℝ) =
          (R : ℝ) ^ 2 * (n.gcd B : ℝ) *
            (((s * s').gcd A * A.divisors.card : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (Nat.cast_nonneg R)]
      ring

/-- The genuinely remaining arithmetic: the `s*s'` gcd and divisor count,
with zero numerators excluded. The `n` and `r` factors of the modulus no
longer occur in this residual sum. -/
def iv3MainResidual (d₁ n₂ n₂' s s' : ℕ) (a h h' : ℤ) (N : ℕ) : ℕ :=
  ∑ n ∈ (Ioc 0 N).filter
      (fun n => iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0),
    (s * s').gcd (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs *
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs.divisors.card

/-- A simultaneous common-index and r mean for the original signed
numerator. It applies even if its slope in the common index vanishes. -/
theorem iv3_main_sqrt_gcd_sum
    {d₁ n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (ha : a ≠ 0) (hn₂ : 0 < n₂) (hn₂' : 0 < n₂')
    (hmain : h' * s ≠ h * s') (N R : ℕ) :
    (∑ n ∈ (Ioc 0 N).filter
        (fun n => iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0),
      ∑ r ∈ Ioc 0 R, Real.sqrt ((n * r * s * s').gcd
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      R * (Real.sqrt ((N *
          (iv3MainConstant n₂ n₂' s s' a h h').natAbs.divisors.card : ℕ) : ℝ) *
        Real.sqrt (iv3MainResidual d₁ n₂ n₂' s s' a h h' N : ℝ)) := by
  let B := (iv3MainConstant n₂ n₂' s s' a h h').natAbs
  let U := (Ioc 0 N).filter
    (fun n => iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0)
  let f := fun n : ℕ => (n.gcd B : ℝ)
  let g := fun n => (((s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs *
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs.divisors.card : ℕ) : ℝ)
  have hf : (∑ n ∈ U, f n) ≤ (N * B.divisors.card : ℕ) := by
    have hsum : (∑ n ∈ U, n.gcd B) ≤ N * B.divisors.card :=
      (sum_le_sum_of_subset (filter_subset _ _)).trans (by
        simpa only [Nat.gcd_comm] using
          sum_gcd_le (Int.natAbs_ne_zero.mpr
            (iv3MainConstant_ne_zero ha hn₂ hn₂' hmain)) N)
    dsimp only [f]
    exact_mod_cast hsum
  have hg : (∑ n ∈ U, g n) =
      (iv3MainResidual d₁ n₂ n₂' s s' a h h' N : ℝ) := by
    simp only [g, U, iv3MainResidual, Nat.cast_sum]
  calc
    _ ≤ ∑ n ∈ U, R * (Real.sqrt (f n) * Real.sqrt (g n)) :=
      sum_le_sum (fun _ hn => iv3_main_sqrt_gcd_r_sum (mem_filter.mp hn).2 R)
    _ = R * ∑ n ∈ U, Real.sqrt (f n) * Real.sqrt (g n) := (mul_sum _ _ _).symm
    _ ≤ R * (Real.sqrt (∑ n ∈ U, f n) * Real.sqrt (∑ n ∈ U, g n)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le U
        (fun _ => by dsimp [f]; positivity) (fun _ => by dsimp [g]; positivity))
        (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [hg]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hf) (Real.sqrt_nonneg _))
        (Nat.cast_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
