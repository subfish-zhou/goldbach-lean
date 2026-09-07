import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationPrimitives
noncomputable section
open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12AnalyticCertificate
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

theorem low_composed_deriv (u : ℝ) (hu : 0 < u) (hb : u ≤ 4/33) :
    HasDerivAt (fun u : ℝ => -lowF ((4/33)/u-1)) (upperDensity u / (1-u)) u := by
  have hn : u ≠ 0 := ne_of_gt hu
  have hx : 0 ≤ (4/33 : ℝ)/u-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hu).2 (by simpa using hb)
  have he : (4/33 : ℝ)/(1+((4/33)/u-1)) = u := by field_simp; ring
  have hk := upperDensity_low_pullback hx
  rw [he] at hk
  have hd := (lowF_deriv ((4/33)/u-1) hx).comp u
    (((hasDerivAt_const u (4/33 : ℝ)).div (hasDerivAt_id u) hn).sub_const 1)
  convert! hd.neg using 1
  rw [← hk]
  simp only [id_eq]
  have hm : 1-u ≠ 0 := by linarith
  field_simp [hn, hm]
  ring

theorem high_composed_deriv (u : ℝ) (hu : 0 < u) (hb : u ≤ 4/33) :
    HasDerivAt (fun u : ℝ => -highF ((4/33)/u-1)) (upperDensity u) u := by
  have hn : u ≠ 0 := ne_of_gt hu
  have hx : 0 ≤ (4/33 : ℝ)/u-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hu).2 (by simpa using hb)
  have he : (4/33 : ℝ)/(1+((4/33)/u-1)) = u := by field_simp; ring
  have hk := upperDensity_pullback hx
  rw [he] at hk
  have hd := (highF_deriv ((4/33)/u-1) hx).comp u
    (((hasDerivAt_const u (4/33 : ℝ)).div (hasDerivAt_id u) hn).sub_const 1)
  convert! hd.neg using 1
  rw [← hk]
  simp only [id_eq]
  have hm : 1-u ≠ 0 := by linarith
  field_simp [hn, hm]
  ring

theorem low_upper_integral_exact :
    (∫ u in (4/53 : ℝ)..(1/10), upperDensity u/(1-u)) =
      lowF (20/33) - lowF (7/33) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => -lowF ((4/33)/u-1))
    (f' := fun u : ℝ => upperDensity u/(1-u))
    (a := (4/53 : ℝ)) (b := (1/10 : ℝ))
    (fun u hu => low_composed_deriv u
      (by rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)] at hu; linarith [hu.1])
      (by rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)] at hu; linarith [hu.2]))
    ((low_continuous upperDensity continuousOn_upperDensity).intervalIntegrable_of_Icc
      (by norm_num))
  norm_num only at h
  convert h using 1; ring

theorem high_upper_integral_exact :
    (∫ u in (1/10 : ℝ)..(4/33), upperDensity u) = highF (7/33) - highF 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => -highF ((4/33)/u-1))
    (f' := upperDensity) (a := (1/10 : ℝ)) (b := (4/33 : ℝ))
    (fun u hu => high_composed_deriv u
      (by rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 4/33)] at hu; linarith [hu.1])
      (by rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 4/33)] at hu; exact hu.2))
    ((continuousOn_upperDensity.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc
      (by norm_num))
  norm_num only at h
  convert h using 1; ring

def endpoints : ℝ :=
  (561990/1000000 : ℝ)*(36/5)*(lowF (20/33)-lowF (7/33)) +
  (564383/1000000 : ℝ)*8*(highF (7/33)-highF 0)

theorem upperMass_eq_endpoints : upperMass = endpoints := by
  unfold upperMass endpoints
  rw [low_upper_integral_exact, high_upper_integral_exact]

end G12AnalyticCertificate
