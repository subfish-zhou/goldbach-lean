import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSignedConsumers

namespace Wu2008DoubleSieve.SecondFunctionalRationalCost
open Set MeasureTheory SecondFunctionalGeometricMass
open SecondFunctionalGeometricMass.Elementary

theorem log_ratio_upper {A B : ℝ} (hB : 0 < B) (hAB : B ≤ A) :
    0 ≤ Real.log (A/B) ∧ Real.log (A/B) ≤ (A-B)/B := by
  have hA := hB.trans_le hAB
  constructor
  · exact Real.log_nonneg ((one_le_div hB).mpr hAB)
  · convert Real.log_le_sub_one_of_pos (div_pos hA hB) using 1; field_simp

 theorem reciprocal_geometry {A B t : ℝ} (hB : 0 < B) (hAB : B ≤ A)
    (ht : t ∈ Icc (1/A) (1/B)) :
    0 < t ∧ B ≤ 1/t ∧ 1/t ≤ A := by
  have hA := hB.trans_le hAB
  have ht0 : 0 < t := (one_div_pos.mpr hA).trans_le ht.1
  refine ⟨ht0, ?_, ?_⟩
  · exact (le_div_iff₀ ht0).mpr (by
      have hh := (le_div_iff₀ hB).mp ht.2
      nlinarith only [hh])
  · exact (div_le_iff₀ ht0).mpr (by
      have hh := (div_le_iff₀ hA).mp ht.1
      nlinarith only [hh])

 theorem log_kernel_upper (n : ℕ) {A B t : ℝ} (hB : 0 < B) (hAB : B ≤ A)
    (ht : t ∈ Icc (1/A) (1/B)) :
    Real.log (t/(1/A))^n * Real.log ((1/B)/t) / t^2 ≤
      ((A-1/t)^n * (1/t-B) / B^(n+1)) / t^2 := by
  obtain ⟨ht0,hBt,htA⟩ := reciprocal_geometry hB hAB ht
  have hx : 0 < 1/t := one_div_pos.mpr ht0
  obtain ⟨hl0,hl⟩ := log_ratio_upper hx htA
  obtain ⟨hr0,hr⟩ := log_ratio_upper hB hBt
  have hleft : Real.log (A/(1/t)) ≤ (A-1/t)/B := hl.trans
    (div_le_div_of_nonneg_left (sub_nonneg.mpr htA) hB hBt)
  have he1 : t/(1/A) = A/(1/t) := by field_simp
  have he2 : (1/B)/t = (1/t)/B := by ring
  rw [he1,he2]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  calc
    _ ≤ ((A-1/t)/B)^n * ((1/t-B)/B) :=
      mul_le_mul (pow_le_pow_left₀ hl0 hleft n) hr hr0
        (pow_nonneg (div_nonneg (sub_nonneg.mpr htA) hB.le) n)
    _ = _ := by rw [div_pow, pow_succ]; ring

noncomputable def reciprocalPrimitive (n : ℕ) (A B t : ℝ) : ℝ :=
  ((A-B)*(A-1/t)^(n+1)/(n+1) - (A-1/t)^(n+2)/(n+2))/B^(n+1)

theorem reciprocalPrimitive_deriv (n : ℕ) {A B t : ℝ} (ht : 0 < t) :
    HasDerivAt (reciprocalPrimitive n A B)
      (((A-1/t)^n*(1/t-B)/B^(n+1))/t^2) t := by
  have hy : HasDerivAt (fun t : ℝ => A-1/t) (1/t^2) t := by
    convert! ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne').const_sub A using 1
    simp only [id_eq]
    ring
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n+2 : ℝ) ≠ 0 := by positivity
  convert! ((((hy.pow (n+1)).const_mul (A-B)).div_const (n+1)).sub
    ((hy.pow (n+2)).div_const (n+2))).div_const (B^(n+1)) using 1
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_sub_cancel,
    show n+2-1=n+1 by omega]
  rw [pow_succ (A-1/t) n]
  field_simp
  ring

 theorem momentOne_upper (n : ℕ) {A B : ℝ} (hB : 0 < B) (hAB : B ≤ A) :
    elementaryMomentOne n (1/A) (1/B) ≤
      (A-B)^(n+2)/((n+1)*(n+2)*B^(n+1)) := by
  have hA := hB.trans_le hAB
  have hab : 1/A ≤ 1/B := one_div_le_one_div_of_le hB hAB
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (FullReduction.logMoment_integrable n 1 (b := 1/B) (one_div_pos.mpr hA))
  have hg : ContinuousOn
      (fun t : ℝ => ((A-1/t)^n*(1/t-B)/B^(n+1))/t^2) (Icc (1/A) (1/B)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.div_const
      apply ContinuousOn.mul
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        exact continuousOn_const.div continuousOn_id (fun t ht => (reciprocal_geometry hB hAB ht).1.ne')
      · exact (continuousOn_const.div continuousOn_id
          (fun t ht => (reciprocal_geometry hB hAB ht).1.ne')).sub continuousOn_const
    · exact continuousOn_id.pow 2
    · intro t ht
      exact pow_ne_zero _ (reciprocal_geometry hB hAB ht).1.ne'
  rw [← logMoment_one_eq n (one_div_pos.mpr hA) hab]
  unfold FullReduction.logMoment
  simp only [pow_one] at hi ⊢
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab hi
    (hg.intervalIntegrable_of_Icc hab) (fun t ht => log_kernel_upper n hB hAB ht)
  apply hm.trans_eq
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => reciprocalPrimitive_deriv n
      (reciprocal_geometry hB hAB (by rwa [uIcc_of_le hab] at ht)).1)
    (hg.intervalIntegrable_of_Icc hab)]
  simp only [reciprocalPrimitive, one_div_one_div, sub_self, zero_pow (by omega : n+1 ≠ 0),
    zero_pow (by omega : n+2 ≠ 0), mul_zero, zero_div, sub_zero]
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  field_simp
  ring

theorem momentZero_upper (n : ℕ) {A B : ℝ} (hB : 0 < B) (hAB : B ≤ A) :
    elementaryMomentZero n (1/A) (1/B) ≤ (A-B)^(n+1)/((n+1)*B^n) := by
  have hA := hB.trans_le hAB
  have hab : 1/A ≤ 1/B := one_div_le_one_div_of_le hB hAB
  have hg : ContinuousOn (fun t : ℝ => ((A-1/t)^n/B^n)/t^2)
      (Icc (1/A) (1/B)) := by
    apply ContinuousOn.div
    · exact ((continuousOn_const.sub (continuousOn_const.div continuousOn_id
        (fun t ht => (reciprocal_geometry hB hAB ht).1.ne'))).pow n).div_const _
    · exact continuousOn_id.pow 2
    · intro t ht
      exact pow_ne_zero _ (reciprocal_geometry hB hAB ht).1.ne'
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt
      (fun t : ℝ => (A-1/t)^(n+1)/((n+1)*B^n)) (((A-1/t)^n/B^n)/t^2) t := by
    have hy : HasDerivAt (fun t : ℝ => A-1/t) (1/t^2) t := by
      convert! ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne').const_sub A using 1
      simp only [id_eq]
      ring
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    convert! (hy.pow (n+1)).div_const ((n+1)*B^n) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    field_simp
  rw [← logMoment_zero_eq n (one_div_pos.mpr hA) hab]
  unfold FullReduction.logMoment
  simp only [pow_zero, mul_one]
  have hm : (∫ t in (1/A)..(1/B), Real.log (t/(1/A))^n/t^2) ≤
      ∫ t in (1/A)..(1/B), ((A-1/t)^n/B^n)/t^2 := by
    apply intervalIntegral.integral_mono_on hab
      (logPower_intervalIntegrable n (one_div_pos.mpr hA) hab)
      (hg.intervalIntegrable_of_Icc hab)
    intro t ht
    obtain ⟨ht0,hBt,htA⟩ := reciprocal_geometry hB hAB ht
    obtain ⟨hl0,hl⟩ := log_ratio_upper (one_div_pos.mpr ht0) htA
    have he : t/(1/A) = A/(1/t) := by field_simp
    rw [he, ← div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    exact pow_le_pow_left₀ hl0 (hl.trans
      (div_le_div_of_nonneg_left (sub_nonneg.mpr htA) hB hBt)) n
  apply hm.trans_eq
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (reciprocal_geometry hB hAB (by rwa [uIcc_of_le hab] at ht)).1)
    (hg.intervalIntegrable_of_Icc hab)]
  simp only [one_div_one_div, sub_self, zero_pow (by omega : n+1 ≠ 0), zero_div, sub_zero]

end Wu2008DoubleSieve.SecondFunctionalRationalCost
