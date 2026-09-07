import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarAnalytic

open Set MeasureTheory Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def s3E (s : ℝ) : ℝ :=
  53 * goldbachS3_innerEnvelope s / (s*((53/8 : ℝ)-s))

noncomputable def s3K (a y : ℝ) : ℝ :=
  -8/(3-a)*(∑ k ∈ range 64, (y/(3-a))^k) +
    360/(29-45*a)*((∑ k ∈ range 64, (45*y/(29-45*a))^k) + (5/2 : ℝ)*(3/5)^64)

theorem s3kernel_majorant {a z : ℝ} (_ha : 0 ≤ a) (haz : a ≤ z)
    (hz : z ≤ 3/5) (_ha5 : a ≤ 1/2) (hu : 45*(z-a)/(29-45*a) ≤ 3/5) :
    -8/(3-z)+360/(29-45*z) ≤ s3K a (z-a) := by
  have hd : 0 < 29-45*a := by linarith
  have he : 0 < 3-a := by linarith
  have hn : 0 ≤ (z-a)/(3-a) := div_nonneg (sub_nonneg.mpr haz) he.le
  have hn1 : (z-a)/(3-a) < 1 := (div_lt_iff₀ he).2 (by linarith)
  have hp : 0 ≤ 45*(z-a)/(29-45*a) := div_nonneg (by linarith) hd.le
  have hlo := mul_le_mul_of_nonpos_left (s3geom_lower hn hn1 64)
    (show -8/(3-a) ≤ 0 by apply div_nonpos_of_nonpos_of_nonneg <;> linarith)
  have hup := mul_le_mul_of_nonneg_left (s3geom_upper hp hu)
    (show 0 ≤ 360/(29-45*a) by positivity)
  have hdz : 29-45*z ≠ 0 := by
    have h := (div_le_iff₀ hd).1 hu
    linarith
  have hez : 3-z ≠ 0 := by linarith
  have hne : 1-(z-a)/(3-a) ≠ 0 := by linarith
  have hnd : 1-45*(z-a)/(29-45*a) ≠ 0 := by linarith
  have en : 1-(z-a)/(3-a) = (3-z)/(3-a) := by field_simp; ring
  have ep : 1-45*(z-a)/(29-45*a) = (29-45*z)/(29-45*a) := by field_simp; ring
  have eqn : -8/(3-a)*(1/(1-(z-a)/(3-a))) = -8/(3-z) := by
    rw [en]
    field_simp
  have eqp : 360/(29-45*a)*(1/(1-45*(z-a)/(29-45*a))) = 360/(29-45*z) := by
    rw [ep]
    field_simp
  rw [eqn] at hlo
  rw [eqp] at hup
  exact add_le_add hlo hup

theorem s3E_continuousOn {l r : ℝ} (hl : 3 ≤ l) (hr : r ≤ 45/8) :
    ContinuousOn s3E (Icc l r) := by
  apply ContinuousOn.div
  · exact continuousOn_const.mul (fun s hs =>
      (goldbachS3_innerEnvelope_hasDerivAt (hl.trans hs.1)).continuousAt.continuousWithinAt)
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro s hs
    apply mul_ne_zero <;> linarith [hs.1, hs.2]

theorem s3segment_bound {l r a : ℝ} (q : List ℚ)
    (hl : 3 ≤ l) (hlr : l ≤ r) (hr : r ≤ 45/8)
    (ha : 0 ≤ a) (ha5 : a ≤ 1/2)
    (hdom : ∀ s ∈ Icc l r, a ≤ (s-3)/(s-1) ∧
      45*((s-3)/(s-1)-a)/(29-45*a) ≤ 3/5)
    (hq : ∀ y : ℝ, s3eval q y =
      (goldbachS3_innerPolynomial 24 48 (a+y)+(a+y)/10^9)*s3K a y) :
    (∫ s in l..r, s3E s) ≤
      s3prim q ((r-3)/(r-1)-a)-s3prim q ((l-3)/(l-1)-a) := by
  let F : ℝ → ℝ := fun s => s3prim q ((s-3)/(s-1)-a)
  let dF : ℝ → ℝ := fun s => s3eval q ((s-3)/(s-1)-a)*(2/(s-1)^2)
  have hd : ∀ s ∈ Icc l r, HasDerivAt F (dF s) s := by
    intro s hs
    have hs1 : s-1 ≠ 0 := by linarith [hs.1]
    have hz : HasDerivAt (fun s : ℝ => (s-3)/(s-1)-a) (2/(s-1)^2) s := by
      apply ((((hasDerivAt_id s).sub_const 3).div
        ((hasDerivAt_id s).sub_const 1) hs1).sub_const a).congr_deriv
      dsimp
      ring
    exact (s3prim_hasDerivAt q _).comp s hz
  apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hlr
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt)
    (s3E_continuousOn hl hr).integrableOn_Icc
  intro s hs
  have hs' : s ∈ Icc l r := ⟨hs.1.le, hs.2.le⟩
  have hs0 : s ∈ Icc (3 : ℝ) (45/8 : ℝ) := ⟨hl.trans hs'.1, hs'.2.trans hr⟩
  have hpos : 0 < s-1 := by linarith [hs0.1]
  have hz0 : 0 ≤ (s-3)/(s-1) := div_nonneg (by linarith [hs0.1]) hpos.le
  have hzu : (s-3)/(s-1) ≤ 3/5 := (div_le_iff₀ hpos).2 (by linarith [hs0.2])
  have hP : 0 ≤ goldbachS3_innerEnvelope s := by
    unfold goldbachS3_innerEnvelope goldbachS3_innerPolynomial
    positivity
  have hk := s3kernel_majorant ha (hdom s hs').1 hzu ha5 (hdom s hs').2
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hP)
    (show 0 ≤ 2/(s-1)^2 by positivity)
  have he : s3E s = goldbachS3_innerEnvelope s *
      (-8/(3-(s-3)/(s-1))+360/(29-45*((s-3)/(s-1))))*(2/(s-1)^2) := by
    rw [mul_assoc, ← s3change_kernel hs0]
    unfold s3E
    ring
  rw [he]
  dsimp [dF]
  rw [hq]
  simpa only [add_sub_cancel, goldbachS3_innerEnvelope] using h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig