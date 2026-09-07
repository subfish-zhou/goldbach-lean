import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarMajorant

open Set MeasureTheory Finset
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The explicit integrated product of the odd logarithm and geometric polynomials. -/
noncomputable def goldbachS3_innerPolynomial (n m : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ i ∈ range n, ∑ j ∈ range m,
    z^(2*i+j+2) / (((2*i+1 : ℕ) : ℝ) * ((2*i+j+2 : ℕ) : ℝ))

/-- Exact derivative of the fixed rational-coefficient polynomial. -/
theorem goldbachS3_innerPolynomial_hasDerivAt (n m : ℕ) (z : ℝ) :
    HasDerivAt (goldbachS3_innerPolynomial n m)
      (2 * (∑ i ∈ range n, z^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
        (∑ j ∈ range m, z^j)) z := by
  have hd : ∀ i j : ℕ,
      HasDerivAt (fun z : ℝ => z^(2*i+j+2) /
        (((2*i+1 : ℕ) : ℝ) * ((2*i+j+2 : ℕ) : ℝ)))
      (z^(2*i+1) / ((2*i+1 : ℕ) : ℝ) * z^j) z := by
    intro i j
    apply ((hasDerivAt_pow (2*i+j+2) z).div_const
      (((2*i+1 : ℕ) : ℝ) * ((2*i+j+2 : ℕ) : ℝ))).congr_deriv
    have h1 : ((2*i+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : ((2*i+j+2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show 2*i+j+2-1 = (2*i+1)+j by omega, pow_add]
    field_simp
  have hh := (HasDerivAt.fun_sum (fun i (_ : i ∈ range n) =>
    HasDerivAt.fun_sum (fun j (_ : j ∈ range m) => hd i j))).const_mul 2
  apply hh.congr_deriv
  simp only [mul_sum, sum_mul, mul_assoc]
  exact sum_comm

/-- A uniform analytic remainder budget on the full transformed S3 range. -/
theorem goldbachS3_log_geometric_remainder {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ 3/5) :
    Real.log ((1+z)/(1-z)) / (1-z) ≤
      2 * (∑ i ∈ range 24, z^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
        (∑ j ∈ range 48, z^j) + 1/10^9 := by
  let L : ℝ := ∑ i ∈ range 24, z^(2*i+1) / ((2*i+1 : ℕ) : ℝ)
  let G : ℝ := ∑ j ∈ range 48, z^j
  have hz1 : z < 1 := by linarith
  have hden : 0 < 1-z := by linarith
  have hsq : 0 < 1-z^2 := by nlinarith
  have hL0 : 0 ≤ L := sum_nonneg (fun i _ => div_nonneg (pow_nonneg hz _) (by positivity))
  have hlog := Real.log_div_le_sum_range_add hz hz1 24
  have hlow := Real.sum_range_le_log_div hz hz1 24
  have heq : G * (1-z) = 1-z^48 := geom_sum_mul_neg z 48
  have hlog3 : Real.log ((1+z)/(1-z)) ≤ 3 := by
    have hx : 0 < (1+z)/(1-z) := div_pos (by linarith) hden
    have h := Real.log_le_sub_one_of_pos hx
    have hr : (1+z)/(1-z) ≤ 4 := (div_le_iff₀ hden).2 (by linarith)
    linarith
  have hL3 : 2*L ≤ 3 := by simpa [L] using (show 2*L ≤ 3 by
    have : L ≤ 1/2 * Real.log ((1+z)/(1-z)) := by simpa [L] using hlow
    linarith)
  have hrem : Real.log ((1+z)/(1-z)) - 2*L ≤ 2*z^49/(1-z^2) := by
    have : 1/2 * Real.log ((1+z)/(1-z)) ≤ L + z^49/(1-z^2) := by
      simpa [L] using hlog
    rw [mul_div_assoc]
    linarith
  have herr : 2*z^49/((1-z^2)*(1-z)) + 3*z^48/(1-z) ≤ (1 : ℝ)/10^9 := by
    have h49 : z^49 ≤ (3/5 : ℝ)^49 := pow_le_pow_left₀ hz hzu _
    have h48 : z^48 ≤ (3/5 : ℝ)^48 := pow_le_pow_left₀ hz hzu _
    have hd1 : (2/5 : ℝ) ≤ 1-z := by linarith
    have hd2 : (16/25 : ℝ) ≤ 1-z^2 := by nlinarith
    calc
      _ ≤ 2*(3/5 : ℝ)^49/((16/25)*(2/5)) + 3*(3/5 : ℝ)^48/(2/5) := by
        gcongr
      _ ≤ (1 : ℝ)/10^9 := by norm_num
  have hstep : Real.log ((1+z)/(1-z)) / (1-z) - 2*L*G ≤
      2*z^49/((1-z^2)*(1-z)) + 3*z^48/(1-z) := by
    have hpoly : 2*L*G*(1-z) = 2*L*(1-z^48) := by rw [mul_assoc, heq]
    have hsmall : 2*L*z^48 ≤ 3*z^48 := mul_le_mul_of_nonneg_right hL3 (pow_nonneg hz _)
    calc
      _ = (Real.log ((1+z)/(1-z)) - 2*L + 2*L*z^48)/(1-z) := by
        apply (eq_div_iff (ne_of_gt hden)).2
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hden), hpoly]
        ring
      _ ≤ (2*z^49/(1-z^2) + 3*z^48)/(1-z) :=
        div_le_div_of_nonneg_right (add_le_add hrem hsmall) hden.le
      _ = _ := by rw [add_div, div_div]
  change Real.log ((1+z)/(1-z)) / (1-z) ≤ 2*L*G + 1/10^9
  linarith

/-- The closed high-accuracy inner-integral envelope. -/
noncomputable def goldbachS3_innerEnvelope (s : ℝ) : ℝ :=
  goldbachS3_innerPolynomial 24 48 ((s-3)/(s-1)) + ((s-3)/(s-1))/10^9

/-- FTC for the actual shifted inner integral, on the domain used below. -/
theorem goldbachS3_inner_hasDerivAt {s : ℝ} (hs : 3 ≤ s) :
    HasDerivAt jurkatRichertInnerIntegral (Real.log (s-2)/(s-1)) s := by
  have he : jurkatRichertInnerIntegral =
      (fun s : ℝ => ∫ t in (3 : ℝ)..s, Real.log (t-2)/(t-1)) := by
    funext s
    exact goldbachS3_inner_shift s
  rw [he]
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact goldbachS3_inner_kernel_continuousOn le_rfl
  · exact ((Real.measurable_log.comp (measurable_id.sub_const 2)).div
      (measurable_id.sub_const 1)).stronglyMeasurable.stronglyMeasurableAtFilter
  · exact ((continuousAt_id.sub continuousAt_const).log (by dsimp; linarith)).div
      (continuousAt_id.sub continuousAt_const) (by dsimp; linarith)

/-- Derivative of the closed envelope without expanding its coefficients. -/
theorem goldbachS3_innerEnvelope_hasDerivAt {s : ℝ} (hs : 3 ≤ s) :
    HasDerivAt goldbachS3_innerEnvelope
      ((2 * (∑ i ∈ range 24, ((s-3)/(s-1))^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
        (∑ j ∈ range 48, ((s-3)/(s-1))^j) + 1/10^9) * (2/(s-1)^2)) s := by
  have hs1 : s-1 ≠ 0 := by linarith
  have hz : HasDerivAt (fun s : ℝ => (s-3)/(s-1)) (2/(s-1)^2) s := by
    apply (((hasDerivAt_id s).sub_const 3).div
      ((hasDerivAt_id s).sub_const 1) hs1).congr_deriv
    dsimp
    ring
  have h := ((goldbachS3_innerPolynomial_hasDerivAt 24 48 ((s-3)/(s-1))).comp s hz).add
    (hz.div_const (10^9))
  apply h.congr_deriv
  ring

/-- The polynomial's derivative dominates the real kernel everywhere, not at sample points. -/
theorem goldbachS3_innerEnvelope_derivative_ge {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) (45/8 : ℝ)) :
    Real.log (s-2)/(s-1) ≤
      ((2 * (∑ i ∈ range 24, ((s-3)/(s-1))^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
        (∑ j ∈ range 48, ((s-3)/(s-1))^j) + 1/10^9) * (2/(s-1)^2)) := by
  let z : ℝ := (s-3)/(s-1)
  have hs1 : 0 < s-1 := by linarith [hs.1]
  have hz : 0 ≤ z := div_nonneg (by linarith [hs.1]) hs1.le
  have hzu : z ≤ 3/5 := (div_le_iff₀ hs1).2 (by linarith [hs.2])
  have h := mul_le_mul_of_nonneg_right (goldbachS3_log_geometric_remainder hz hzu)
    (show 0 ≤ 2/(s-1)^2 by positivity)
  have he1 : (1+z)/(1-z) = s-2 := by
    dsimp [z]
    field_simp
    ring
  have he2 : Real.log ((1+z)/(1-z))/(1-z) * (2/(s-1)^2) =
      Real.log (s-2)/(s-1) := by
    rw [he1]
    dsimp [z]
    field_simp
    ring
  rw [he2] at h
  exact h

/-- A fixed rational-coefficient, whole-interval envelope for the actual inner integral. -/
theorem goldbachS3_inner_le_envelope {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) (45/8 : ℝ)) :
    jurkatRichertInnerIntegral s ≤ goldbachS3_innerEnvelope s := by
  let D : Set ℝ := Icc 3 (45/8)
  let F : ℝ → ℝ := fun s => goldbachS3_innerEnvelope s - jurkatRichertInnerIntegral s
  let dF : ℝ → ℝ := fun s =>
    ((2 * (∑ i ∈ range 24, ((s-3)/(s-1))^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
      (∑ j ∈ range 48, ((s-3)/(s-1))^j) + 1/10^9) * (2/(s-1)^2)) -
      Real.log (s-2)/(s-1)
  have hd : ∀ x ∈ D, HasDerivAt F (dF x) x := fun x hx =>
    (goldbachS3_innerEnvelope_hasDerivAt hx.1).sub (goldbachS3_inner_hasDerivAt hx.1)
  have hm : MonotoneOn F D := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => sub_nonneg.mpr (goldbachS3_innerEnvelope_derivative_ge (interior_subset hx)))
  have h := hm (show (3 : ℝ) ∈ D by constructor <;> norm_num) hs hs.1
  have hzero : F 3 = 0 := by
    simp [F, goldbachS3_innerEnvelope, goldbachS3_innerPolynomial, jurkatRichertInnerIntegral]
    norm_num
  rw [hzero] at h
  exact sub_nonneg.mp h

/-- The same fixed product polynomial is a lower derivative bound. -/
theorem goldbachS3_log_geometric_lower {z : ℝ} (hz : 0 ≤ z) (hzu : z < 1) :
    2 * (∑ i ∈ range 24, z^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
      (∑ j ∈ range 48, z^j) ≤ Real.log ((1+z)/(1-z))/(1-z) := by
  let L : ℝ := ∑ i ∈ range 24, z^(2*i+1) / ((2*i+1 : ℕ) : ℝ)
  let G : ℝ := ∑ j ∈ range 48, z^j
  have hL0 : 0 ≤ L := sum_nonneg (fun i _ => div_nonneg (pow_nonneg hz _) (by positivity))
  have hlog : 2*L ≤ Real.log ((1+z)/(1-z)) := by
    have h := Real.sum_range_le_log_div hz hzu 24
    have : L ≤ 1/2 * Real.log ((1+z)/(1-z)) := by simpa [L] using h
    linarith
  have heq : G*(1-z) = 1-z^48 := geom_sum_mul_neg z 48
  apply (le_div_iff₀ (show 0 < 1-z by linarith)).2
  change 2*L*G*(1-z) ≤ Real.log ((1+z)/(1-z))
  rw [mul_assoc, heq]
  nlinarith [mul_nonneg hL0 (pow_nonneg hz 48)]

/-- The transformed polynomial also lies below the actual inner integral. -/
theorem goldbachS3_innerPolynomial_le_inner {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) (45/8 : ℝ)) :
    goldbachS3_innerPolynomial 24 48 ((s-3)/(s-1)) ≤ jurkatRichertInnerIntegral s := by
  let P : ℝ → ℝ := fun s => goldbachS3_innerPolynomial 24 48 ((s-3)/(s-1))
  let dP : ℝ → ℝ := fun s =>
    (2 * (∑ i ∈ range 24, ((s-3)/(s-1))^(2*i+1) / ((2*i+1 : ℕ) : ℝ)) *
      (∑ j ∈ range 48, ((s-3)/(s-1))^j)) * (2/(s-1)^2)
  have hP : ∀ s : ℝ, 3 ≤ s → HasDerivAt P (dP s) s := by
    intro s hs
    have hz : HasDerivAt (fun s : ℝ => (s-3)/(s-1)) (2/(s-1)^2) s := by
      apply (((hasDerivAt_id s).sub_const 3).div
        ((hasDerivAt_id s).sub_const 1) (show s-1 ≠ 0 by linarith)).congr_deriv
      dsimp
      ring
    exact (goldbachS3_innerPolynomial_hasDerivAt 24 48 _).comp s hz
  have hle : ∀ s ∈ Icc (3 : ℝ) (45/8 : ℝ), dP s ≤ Real.log (s-2)/(s-1) := by
    intro s hs
    let z : ℝ := (s-3)/(s-1)
    have hs1 : 0 < s-1 := by linarith [hs.1]
    have hz : 0 ≤ z := div_nonneg (by linarith [hs.1]) hs1.le
    have hzu : z < 1 := (div_lt_iff₀ hs1).2 (by linarith)
    have h := mul_le_mul_of_nonneg_right (goldbachS3_log_geometric_lower hz hzu)
      (show 0 ≤ 2/(s-1)^2 by positivity)
    have he1 : (1+z)/(1-z) = s-2 := by dsimp [z]; field_simp; ring
    have he2 : Real.log ((1+z)/(1-z))/(1-z) * (2/(s-1)^2) =
        Real.log (s-2)/(s-1) := by rw [he1]; dsimp [z]; field_simp; ring
    rw [he2] at h
    exact h
  let F : ℝ → ℝ := fun s => jurkatRichertInnerIntegral s - P s
  let dF : ℝ → ℝ := fun s => Real.log (s-2)/(s-1) - dP s
  have hd : ∀ s ∈ Icc (3 : ℝ) (45/8 : ℝ), HasDerivAt F (dF s) s :=
    fun s hs => (goldbachS3_inner_hasDerivAt hs.1).sub (hP s hs.1)
  have hm : MonotoneOn F (Icc (3 : ℝ) (45/8 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => sub_nonneg.mpr (hle s (interior_subset hs)))
  have h := hm (show (3 : ℝ) ∈ Icc (3 : ℝ) (45/8 : ℝ) by constructor <;> norm_num) hs hs.1
  have hzero : F 3 = 0 := by
    simp [F, P, goldbachS3_innerPolynomial, jurkatRichertInnerIntegral]
    norm_num
  rw [hzero] at h
  exact sub_nonneg.mp h

/-- Two-sided, uniform certification of the approximation error. -/
theorem goldbachS3_innerEnvelope_error {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) (45/8 : ℝ)) :
    0 ≤ goldbachS3_innerEnvelope s - jurkatRichertInnerIntegral s ∧
      goldbachS3_innerEnvelope s - jurkatRichertInnerIntegral s ≤ 3/(5*10^9) := by
  constructor
  · exact sub_nonneg.mpr (goldbachS3_inner_le_envelope hs)
  · have h := goldbachS3_innerPolynomial_le_inner hs
    have hs1 : 0 < s-1 := by linarith [hs.1]
    have hz : (s-3)/(s-1) ≤ (3/5 : ℝ) := (div_le_iff₀ hs1).2 (by linarith [hs.2])
    unfold goldbachS3_innerEnvelope
    linarith

/-- A closed rational majorant of the entire original piecewise numerator. -/
noncomputable def goldbachS3_fullEnvelope (s : ℝ) : ℝ :=
  (1 + goldbachS3_innerEnvelope (max s 3) + (max (s-5) 0)^4 / 576) /
    (s * ((53/8 : ℝ)-s))

/-- Whole-interval majorization of the actual exp-free integrand by a closed expression. -/
theorem goldbachS3_fullEnvelope_majorizes {s : ℝ}
    (hs : s ∈ Icc (53/24 : ℝ) (45/8 : ℝ)) :
    (if s ≤ 3 then 1 else if s ≤ 5 then 1 + jurkatRichertInnerIntegral s else
      1 + jurkatRichertInnerIntegral 5 +
        ∫ t in (5 : ℝ)..s,
          (Real.log (t-2) + ∫ v in (3 : ℝ)..t-2,
            jurkatRichertInnerIntegral v / v) / (t-1)) /
      (s * ((53/8 : ℝ)-s)) ≤ goldbachS3_fullEnvelope s := by
  unfold goldbachS3_fullEnvelope
  apply div_le_div_of_nonneg_right _ (by nlinarith [hs.1, hs.2])
  split_ifs with h3 h5
  · rw [max_eq_right h3, max_eq_right (by linarith : s-5 ≤ 0)]
    simp [goldbachS3_innerEnvelope, goldbachS3_innerPolynomial]
  · rw [max_eq_left (by linarith : 3 ≤ s), max_eq_right (by linarith : s-5 ≤ 0)]
    have h := goldbachS3_inner_le_envelope ⟨by linarith, hs.2⟩
    norm_num
    linarith
  · rw [max_eq_left (by linarith : 3 ≤ s), max_eq_left (by linarith : 0 ≤ s-5),
      goldbachS3_third_body_split (by linarith : 5 ≤ s)]
    linarith [goldbachS3_inner_le_envelope ⟨by linarith, hs.2⟩,
      goldbachS3_nested_quartic_majorant (by linarith : 5 ≤ s)]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig