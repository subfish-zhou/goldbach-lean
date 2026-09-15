import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerPositive
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureEndpoint

namespace Wu2008DoubleSieve.TruncatedSixthPositiveGain
open Set Real MeasureTheory
open scoped Classical

/-- The rectangle is fixed before the proof and lies in the original admissible region. -/
theorem rectangle_geometry {x y : ℝ} (hx : x ∈ Icc (1/10 : ℝ) (11/100))
    (hy : y ∈ Icc (1/5 : ℝ) (21/100)) :
    truncatedSixthLowerAdmissibleRegion (1/1000) x y ∧
      truncatedSixthLowerS (1/1000) x y ∈ Icc (2 : ℝ) 3 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor
  · unfold truncatedSixthLowerAdmissibleRegion truncatedSixthLowerRegion
      truncatedSixthLowerAlpha truncatedSixthLowerBeta truncatedSixthLowerSigma
      truncatedSixthLowerC
    norm_num [truncatedSixthLowerAlpha]
    exact ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩,
      by linarith⟩
  · unfold truncatedSixthLowerS truncatedSixthLowerC truncatedSixthLowerAlpha
    constructor <;> norm_num <;> linarith

/-- All denominator factors are positive and bounded by the prescribed rational factors. -/
theorem rectangle_denominator {x y : ℝ} (hx : x ∈ Icc (1/10 : ℝ) (11/100))
    (hy : y ∈ Icc (1/5 : ℝ) (21/100)) :
    0 < x * y * (truncatedSixthLowerC (1/1000) - x - y) ∧
    x * y * (truncatedSixthLowerC (1/1000) - x - y) ≤
      (11/100 : ℝ) * (21/100) * (199/1000) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hz0 : 0 < truncatedSixthLowerC (1/1000) - x - y := by
    unfold truncatedSixthLowerC
    linarith [hx.2, hy.2]
  have hz1 : truncatedSixthLowerC (1/1000) - x - y ≤ (199/1000 : ℝ) := by
    unfold truncatedSixthLowerC
    linarith [hx.1, hy.1]
  exact ⟨mul_pos (mul_pos hx0 hy0) hz0,
    mul_le_mul (mul_le_mul hx.2 hy.2 hy0.le (by norm_num)) hz1 hz0.le
      (by norm_num)⟩

/-- The actual lower-improvement seed is consumed pointwise, without continuity. -/
theorem rectangle_kernel_lower {x y : ℝ} (hx : x ∈ Icc (1/10 : ℝ) (11/100))
    (hy : y ∈ Icc (1/5 : ℝ) (21/100)) :
    (1/1500 : ℝ) / ((11/100) * (21/100) * (199/1000)) ≤
      truncatedSixthMassHKernel (1/1000) (x,y) := by
  obtain ⟨ha, hs⟩ := rectangle_geometry hx hy
  obtain ⟨hd0, hd1⟩ := rectangle_denominator hx hy
  rw [truncatedSixthMassHKernel, if_pos ha]
  have hh := (SecondFunctionalLowerPositive.h_interval_strict hs.1 hs.2).le
  exact div_le_div₀ (by linarith) hh hd0 hd1

/-- The true area of the prescribed rectangle, computed in the product volume measure. -/
theorem rectangle_area :
    volume.real (Icc (1/10 : ℝ) (11/100) ×ˢ Icc (1/5 : ℝ) (21/100)) =
      (1/10000 : ℝ) := by
  rw [measureReal_def]
  change ((volume.prod volume) _).toReal = _
  rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ENNReal.toReal_mul]
  norm_num

/-- Genuine subrectangle integration, followed by comparison with the entire original kernel. -/
theorem rectangle_integral_lower :
    (1/10000 : ℝ) * ((1/1500) / ((11/100) * (21/100) * (199/1000))) ≤
      ∫ v : ℝ × ℝ, truncatedSixthMassHKernel (1/1000) v := by
  let R : Set (ℝ × ℝ) := Icc (1/10 : ℝ) (11/100) ×ˢ Icc (1/5 : ℝ) (21/100)
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hfin : volume R ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi := (truncatedSixthMass_kernels_integrable
    (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num)).2
  have hc : IntegrableOn (fun _ : ℝ × ℝ =>
      (1/1500 : ℝ) / ((11/100) * (21/100) * (199/1000))) R :=
    integrableOn_const hfin
  have hsub := setIntegral_mono_on hc hi.integrableOn hR
    (fun v hv => rectangle_kernel_lower hv.1 hv.2)
  have hnonneg : ∀ v : ℝ × ℝ, 0 ≤ truncatedSixthMassHKernel (1/1000) v :=
    fun v => (truncatedSixthMass_kernels_bounds (by norm_num) (by norm_num) v).2.1
  have hwhole := setIntegral_le_integral (s := R) hi (Filter.Eventually.of_forall hnonneg)
  rw [setIntegral_const, smul_eq_mul] at hsub
  change volume.real (Icc (1/10 : ℝ) (11/100) ×ˢ Icc (1/5 : ℝ) (21/100)) * _ ≤ _ at hsub
  rw [rectangle_area] at hsub
  exact hsub.trans hwhole

/-- The original admissible gain, retaining the original outer coefficient four. -/
theorem hadmdelta_lower :
    (8/137907 : ℝ) ≤ truncatedSixthLowerHadmdelta (1/1000) := by
  rw [(truncatedSixthMass_literal_integrals (by norm_num) (by norm_num)).2]
  have h := mul_le_mul_of_nonneg_left rectangle_integral_lower (by norm_num : (0 : ℝ) ≤ 4)
  norm_num at h ⊢
  exact h

/-- The original actual truncated-sixth count, with the same delta and no extra epsilon loss. -/
theorem actual_count_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerFdelta (1/1000) + 8/137907 - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT4, hT⟩ := truncatedSixthClosure_actual_lower
    (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  have hc : truncatedSixthLowerFdelta (1/1000) + 8/137907 - ε ≤
      truncatedSixthLowerFdelta (1/1000) + truncatedSixthLowerHadmdelta (1/1000) - ε := by
    linarith [hadmdelta_lower]
  have hs := truncatedSixthClosure_scale_nonneg (hT4.trans hN)
  have h := mul_le_mul_of_nonneg_right hc hs
  have hmain : (truncatedSixthLowerFdelta (1/1000) + 8/137907 - ε) *
      wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthLowerFdelta (1/1000) + truncatedSixthLowerHadmdelta (1/1000) - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using h
  exact hmain.trans (hT N hN he)

/-- Definitional confirmation: this is precisely the original iterated integral. -/
theorem hadmdelta_object : truncatedSixthLowerHadmdelta (1/1000) =
    4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
      ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
        if truncatedSixthLowerAdmissibleRegion (1/1000) x y then
          wuImprovementLimit false (1/1000) (truncatedSixthLowerS (1/1000) x y) /
            (x * y * (truncatedSixthLowerC (1/1000) - x - y)) else 0 := rfl

/-- Definitional confirmation of the actual finite count and its unchanged atom. -/
theorem actual_count_object (N : ℕ) :
    truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
      ((N : ℝ) ^ truncatedSixthLowerLambda) =
    ∑ t ∈ truncatedSixthKept N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
      ((N : ℝ) ^ truncatedSixthLowerLambda),
      sieveCount N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) := rfl

/-- The classical term stays the original fixed-delta canonical lower coefficient. -/
theorem fdelta_object : truncatedSixthLowerFdelta (1/1000) =
    4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
      ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
        if truncatedSixthLowerRegion (1/1000) x y then
          wuLowerCoefficient (truncatedSixthLowerS (1/1000) x y) /
            (x * y * (truncatedSixthLowerC (1/1000) - x - y)) else 0 := rfl

end Wu2008DoubleSieve.TruncatedSixthPositiveGain
