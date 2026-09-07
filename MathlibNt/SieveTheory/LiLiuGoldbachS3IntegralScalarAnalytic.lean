import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarPolynomial

open Set MeasureTheory Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Dense exact rational polynomial, in increasing coefficient order. -/
noncomputable def s3eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * s3eval cs x

/-- A rational primitive; the natural offset makes the derivative induction transparent. -/
noncomputable def s3primAux : List ℚ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, n, x => (c : ℝ) / (n+1 : ℕ) * x^(n+1) + s3primAux cs (n+1) x

noncomputable def s3prim (cs : List ℚ) : ℝ → ℝ := s3primAux cs 0

theorem s3eval_continuous (cs : List ℚ) : Continuous (s3eval cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih => exact continuous_const.add (continuous_id.mul ih)

theorem s3primAux_hasDerivAt (cs : List ℚ) (n : ℕ) (x : ℝ) :
    HasDerivAt (s3primAux cs n) (x^n * s3eval cs x) x := by
  induction cs generalizing n with
  | nil => simpa [s3primAux, s3eval] using (hasDerivAt_const x (0 : ℝ))
  | cons c cs ih =>
    have h := (((hasDerivAt_pow (n+1) x).const_mul ((c : ℝ)/(n+1 : ℕ))).add
      (ih (n+1)))
    apply h.congr_deriv
    simp only [s3eval, Nat.add_sub_cancel, pow_succ]
    have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp

theorem s3prim_hasDerivAt (cs : List ℚ) (x : ℝ) :
    HasDerivAt (s3prim cs) (s3eval cs x) x := by
  simpa [s3prim] using s3primAux_hasDerivAt cs 0 x

/-- Finite geometric lower bound, valid on the entire interval. -/
theorem s3geom_lower {x : ℝ} (hx : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ k ∈ range n, x^k) ≤ 1/(1-x) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-x)).2
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hx n]

/-- Fixed-order geometric upper bound, with uniform analytic remainder. -/
theorem s3geom_upper {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 3/5) :
    1/(1-x) ≤ (∑ k ∈ range 64, x^k) + (5/2 : ℝ)*(3/5)^64 := by
  have hd : 0 < 1-x := by linarith
  apply (div_le_iff₀ hd).2
  rw [add_mul, geom_sum_mul_neg]
  have hp := pow_le_pow_left₀ hx hu 64
  have hp0 : (0 : ℝ) ≤ (3/5)^64 := by positivity
  nlinarith

/-- The exact transformed Jacobian-kernel identity. -/
theorem s3change_kernel {s : ℝ} (hs : s ∈ Icc (3 : ℝ) (45/8 : ℝ)) :
    53/(s*((53/8 : ℝ)-s)) =
      (-8/(3-(s-3)/(s-1)) + 360/(29-45*((s-3)/(s-1)))) * (2/(s-1)^2) := by
  have h1 : s-1 ≠ 0 := by linarith [hs.1]
  have h2 : s ≠ 0 := by linarith [hs.1]
  have h3 : (53 : ℝ)/8-s ≠ 0 := by linarith [hs.2]
  have h4 : (53 : ℝ)-s*8 ≠ 0 := by linarith [hs.2]
  have h5 : (106 : ℝ)-s*16 ≠ 0 := by linarith [hs.2]
  have he1 : 3-(s-3)/(s-1) = 2*s/(s-1) := by field_simp; ring
  have he2 : 29-45*((s-3)/(s-1)) = (106-16*s)/(s-1) := by field_simp; ring
  have h6 : (106 : ℝ)-16*s ≠ 0 := by linarith [hs.2]
  rw [he1, he2]
  field_simp [h1, h2, h3, h4, h5, h6]
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig