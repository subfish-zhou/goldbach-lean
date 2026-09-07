import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Piecewise

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace G67Analytic

/-- The odd Taylor polynomial for twice the inverse hyperbolic tangent.
The degree is a symbolic parameter; no degree search is involved. -/
def A : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, x => A n x + 2 * x^(2*n+1) / (2*n+1)

/-- Its derivative, retained in recursive factored form. -/
def B : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, x => B n x + 2 * x^(2*n)

theorem A_zero (n : ℕ) : A n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [A, ih]

theorem A_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ A n x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg ih (by positivity)

theorem A_deriv (n : ℕ) (x : ℝ) : HasDerivAt (A n) (B n x) x := by
  induction n with
  | zero => exact hasDerivAt_const x 0
  | succ n ih =>
    have h : HasDerivAt (fun y : ℝ => 2 * y^(2*n+1) / (2*n+1))
        (2 * x^(2*n)) x := by
      convert (((hasDerivAt_id x).pow (2*n+1)).const_mul 2).div_const
        (2*(n:ℝ)+1) using 1 <;> first | rfl | skip
      simp only [Nat.add_sub_cancel, mul_one, id_eq]
      push_cast
      field_simp
    exact ih.add h

theorem B_residual (n : ℕ) (x : ℝ) :
    (1-x^2) * B n x = 2 * (1-x^(2*n)) := by
  induction n with
  | zero => simp [B]
  | succ n ih =>
    rw [B, mul_add, ih]
    rw [show 2*(n+1) = 2*n+2 by omega, pow_add]
    ring

/-- The polynomial is below the logarithmic ratio throughout its analytic domain. -/
theorem A_le_log_ratio (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hX : x < 1) :
    A n x ≤ Real.log (1+x) - Real.log (1-x) := by
  let F : ℝ → ℝ := fun y => Real.log (1+y) - Real.log (1-y) - A n y
  have hd : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt F (1/(1+y) + 1/(1-y) - B n y) y := by
    intro y hy
    have hp : 1+y ≠ 0 := by linarith [hy.1]
    have hm : 1-y ≠ 0 := by linarith [hy.2]
    convert ((((hasDerivAt_id y).const_add 1).log hp).sub
      (((hasDerivAt_id y).const_sub 1).log hm)).sub (A_deriv n y) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hn : ∀ y ∈ Icc (0 : ℝ) x,
      0 ≤ 1/(1+y) + 1/(1-y) - B n y := by
    intro y hy
    have hp : 0 < 1+y := by linarith [hy.1]
    have hm : 0 < 1-y := by linarith [hy.2]
    have hden : 0 < 1-y^2 := by nlinarith [mul_pos hp hm]
    have he : 1/(1+y) + 1/(1-y) - B n y =
        2*y^(2*n)/(1-y^2) := by
      apply (eq_div_iff hden.ne').2
      have hsum : (1/(1+y) + 1/(1-y)) * (1-y^2) = 2 := by
        field_simp
        ring
      nlinarith only [hsum, B_residual n y]
    rw [he]
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hy.1 _)) hden.le
  have hmono : MonotoneOn F (Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hn y (interior_subset hy))
  have hh := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F, A_zero] using hh

/-- A log-free rational lower envelope, valid for every order. -/
def logLower (n : ℕ) (z : ℝ) : ℝ := A n ((z-1)/(z+1))

theorem logLower_nonneg (n : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    0 ≤ logLower n z := by
  exact A_nonneg n (div_nonneg (by linarith) (by linarith))

theorem logLower_le_log (n : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    logLower n z ≤ Real.log z := by
  have hp : 0 < z+1 := by linarith
  have ht : 0 ≤ (z-1)/(z+1) := div_nonneg (by linarith) hp.le
  have hT : (z-1)/(z+1) < 1 := (div_lt_one hp).2 (by linarith)
  have h := A_le_log_ratio n ht hT
  have hm : 1-(z-1)/(z+1) ≠ 0 := by linarith
  rw [← Real.log_div (by linarith : 1+(z-1)/(z+1) ≠ 0) hm] at h
  have he : (1+(z-1)/(z+1))/(1-(z-1)/(z+1)) = z := by
    field_simp
    ring
  rw [he] at h
  exact h

/-- Polynomial-envelope continuity uses its certified derivative. -/
theorem logLower_continuousOn (n : ℕ) : ContinuousOn (logLower n) (Ici 1) := by
  have hc : Continuous (A n) := continuous_iff_continuousAt.mpr
    (fun x => (A_deriv n x).continuousAt)
  exact hc.comp_continuousOn ((continuousOn_id.sub continuousOn_const).div
    (continuousOn_id.add continuousOn_const) (fun z hz => by change z + 1 ≠ 0; have hh : 1 ≤ z := hz; linarith))

/-- The profile envelope preserves the full original logarithm. -/
def profileLower (n : ℕ) (s : ℝ) : ℝ :=
  logLower n (((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ))/(1/2-s)

theorem profileLower_le (n : ℕ) {s : ℝ}
    (hs : s ≤ (1/2 : ℝ)-2*(4/53 : ℝ)) :
    profileLower n s ≤ G67SumCoordinate.profile s := by
  have hD : 0 < (1/2 : ℝ)-s := by linarith
  have hZ : 1 ≤ ((1/2-s)-(4/53 : ℝ))/(4/53 : ℝ) := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4/53)).2
    linarith
  exact (div_le_div_of_nonneg_right (logLower_le_log n hZ) hD.le).trans
    (le_max_right _ _)

end G67Analytic
