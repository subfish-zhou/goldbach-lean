import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real Set MeasureTheory intervalIntegral

namespace AnalyticNumberTheory.LargeSieve

/-- A totalized version of the damped Perron majorant.  The explicit zero branch keeps the
paper expression honest even though division by zero is totalized in Lean. -/
noncomputable def dampedPerronMajorantIntegrand (ε L t : ℝ) : ℝ :=
  if t = 0 then 0 else Real.exp (-ε * t) * min 1 (L * t) / t

lemma dampedPerronMajorantIntegrand_measurable (ε L : ℝ) : Measurable (dampedPerronMajorantIntegrand ε L) := by
  unfold dampedPerronMajorantIntegrand
  apply Measurable.ite (by simpa only [Set.ofPred_eq_eq_singleton] using measurableSet_singleton (0 : ℝ))
  · fun_prop
  · fun_prop

lemma dampedPerronMajorantIntegrand_nonneg {ε L t : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) :
    0 ≤ dampedPerronMajorantIntegrand ε L t := by
  by_cases h0 : t = 0
  · simp [dampedPerronMajorantIntegrand, h0]
  · rw [dampedPerronMajorantIntegrand, if_neg h0]
    positivity

lemma dampedPerronMajorantIntegrand_le_head {ε L t : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (ht : t ∈ Ioc (0 : ℝ) 1) : dampedPerronMajorantIntegrand ε L t ≤ L := by
  rw [dampedPerronMajorantIntegrand, if_neg ht.1.ne']
  have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1.le])
  have hm0 : 0 ≤ min 1 (L * t) := le_min zero_le_one (mul_nonneg hL ht.1.le)
  have hm : min 1 (L * t) ≤ L * t := min_le_right _ _
  rw [div_le_iff₀ ht.1]
  nlinarith [Real.exp_pos (-ε * t)]

lemma dampedPerronMajorantIntegrand_le_inv {ε L t : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (ht : 1 ≤ t) : dampedPerronMajorantIntegrand ε L t ≤ t⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [dampedPerronMajorantIntegrand, if_neg ht0.ne']
  have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hm0 : 0 ≤ min 1 (L * t) := le_min zero_le_one (mul_nonneg hL ht0.le)
  have hm : min 1 (L * t) ≤ 1 := min_le_left _ _
  rw [div_eq_mul_inv]
  have hi : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hp : Real.exp (-ε * t) * min 1 (L * t) ≤ 1 := by
    nlinarith [Real.exp_pos (-ε * t)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hi

lemma dampedPerronMajorantIntegrand_le_tail {ε L t : ℝ} (hε : 0 < ε) (_hL : 0 ≤ L)
    (ht : ε⁻¹ ≤ t) : dampedPerronMajorantIntegrand ε L t ≤ ε * Real.exp (-ε * t) := by
  have ht0 : 0 < t := (inv_pos.mpr hε).trans_le ht
  have hi : t⁻¹ ≤ ε := by
    rw [inv_le_comm₀ ht0 hε]
    simpa [one_div] using ht
  calc
    dampedPerronMajorantIntegrand ε L t ≤ t⁻¹ * Real.exp (-ε * t) := by
      rw [dampedPerronMajorantIntegrand, if_neg ht0.ne', div_eq_mul_inv]
      have hm : min 1 (L * t) ≤ 1 := min_le_left _ _
      have he0 : 0 ≤ Real.exp (-ε * t) := (Real.exp_pos _).le
      have hi0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
      nlinarith [mul_le_mul_of_nonneg_left hm he0]
    _ ≤ ε * Real.exp (-ε * t) := by
      gcongr

lemma dampedPerronMajorant_integrableOn_head {ε L : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    IntegrableOn (dampedPerronMajorantIntegrand ε L) (Ioc (0 : ℝ) 1) := by
  apply (integrableOn_const (μ := volume) (C := L)
    ((measure_Ioc_lt_top (μ := volume) : volume (Ioc (0 : ℝ) 1) < ⊤).ne)).mono'
  · exact (dampedPerronMajorantIntegrand_measurable ε L).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (dampedPerronMajorantIntegrand_nonneg hL ht.1.le)]
    exact dampedPerronMajorantIntegrand_le_head hL hε ht

lemma dampedPerronMajorant_integrableOn_tail {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    IntegrableOn (dampedPerronMajorantIntegrand ε L) (Ioi (1 : ℝ)) := by
  apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 1).mono'
  · exact (dampedPerronMajorantIntegrand_measurable ε L).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (dampedPerronMajorantIntegrand_nonneg hL (zero_lt_one.trans ht).le)]
    rw [dampedPerronMajorantIntegrand, if_neg (zero_lt_one.trans ht).ne', div_eq_mul_inv]
    have hm : min 1 (L * t) ≤ 1 := min_le_left _ _
    have hi : t⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans ht)).mpr ht.le
    have he0 : 0 ≤ Real.exp (-ε * t) := (Real.exp_pos _).le
    have hm0 : 0 ≤ min 1 (L * t) :=
      le_min zero_le_one (mul_nonneg hL (zero_lt_one.trans ht).le)
    nlinarith [mul_le_mul_of_nonneg_left hm he0,
      mul_le_mul_of_nonneg_left hi (mul_nonneg he0 hm0)]

/-- Integrability on the positive half-line, obtained without any unproved limiting assertion. -/
theorem dampedPerronMajorant_integrableOn_Ioi {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    IntegrableOn (dampedPerronMajorantIntegrand ε L) (Ioi (0 : ℝ)) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h
      by_cases ht : t ≤ 1 <;> aesop
    · rintro (h | h) <;> linarith]
  exact (dampedPerronMajorant_integrableOn_head hL hε.le).union (dampedPerronMajorant_integrableOn_tail hε hL)

/-- The `(0,1]` contribution. -/
theorem dampedPerronMajorant_integral_head_le {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    (∫ t in Ioc (0 : ℝ) 1, dampedPerronMajorantIntegrand ε L t) ≤ L := by
  calc
    (∫ t in Ioc (0 : ℝ) 1, dampedPerronMajorantIntegrand ε L t) ≤ ∫ _t in Ioc (0 : ℝ) 1, L := by
      apply MeasureTheory.integral_mono_ae
      · exact dampedPerronMajorant_integrableOn_head hL hε.le
      · exact integrableOn_const (μ := volume)
          ((measure_Ioc_lt_top (μ := volume) : volume (Ioc (0 : ℝ) 1) < ⊤).ne)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact dampedPerronMajorantIntegrand_le_head hL hε.le ht
    _ = L := by norm_num

/-- The `[1,1/ε]` logarithmic contribution. -/
theorem dampedPerronMajorant_integral_middle_le {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L) :
    (∫ t in Ioc (1 : ℝ) ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤ Real.log (ε⁻¹) := by
  have hb : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  calc
    (∫ t in Ioc (1 : ℝ) ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤ ∫ t in Ioc (1 : ℝ) ε⁻¹, t⁻¹ := by
      apply MeasureTheory.integral_mono_ae
      · exact (dampedPerronMajorant_integrableOn_Ioi hε hL).mono (fun t ht => zero_lt_one.trans ht.1) le_rfl
      · exact ((continuousOn_inv₀.mono (by
          intro t ht
          simp only [mem_compl_iff, mem_singleton_iff]
          linarith [ht.1])).integrableOn_Icc (μ := volume)).mono Ioc_subset_Icc_self le_rfl
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact dampedPerronMajorantIntegrand_le_inv hε.le hL ht.1.le
    _ = Real.log (ε⁻¹) := by
      rw [← intervalIntegral.integral_of_le hb, integral_inv_of_pos zero_lt_one (inv_pos.mpr hε)]
      simp

/-- The exponentially damped tail beginning at `1/ε`. -/
theorem dampedPerronMajorant_integral_tail_le_one {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    (∫ t in Ioi ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤ 1 := by
  calc
    (∫ t in Ioi ε⁻¹, dampedPerronMajorantIntegrand ε L t) ≤
        ∫ t in Ioi ε⁻¹, ε * Real.exp (-ε * t) := by
      apply MeasureTheory.integral_mono_ae
      · exact (dampedPerronMajorant_integrableOn_Ioi hε hL).mono (Ioi_subset_Ioi (inv_pos.mpr hε).le) le_rfl
      · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) ε⁻¹).const_mul ε
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact dampedPerronMajorantIntegrand_le_tail hε hL ht.le
    _ = Real.exp (-1) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hε)]
      rw [show -ε * ε⁻¹ = -1 by field_simp]
      field_simp
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

/-- The full damped Perron majorant bound. -/
theorem dampedPerronMajorant_integral_Ioi_le {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L) :
    (∫ t in Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L t) ≤ L + Real.log (1 / ε) + 1 := by
  have hb : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  let s₀ : Set ℝ := Ioc 0 1
  let s₁ : Set ℝ := Ioc 1 ε⁻¹
  let s₂ : Set ℝ := Ioi ε⁻¹
  have hs : Ioi (0 : ℝ) = s₀ ∪ (s₁ ∪ s₂) := by
    ext t
    simp only [s₀, s₁, s₂, mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases h₀ : t ≤ 1
      · exact Or.inl ⟨ht, h₀⟩
      · by_cases h₁ : t ≤ ε⁻¹
        · exact Or.inr (Or.inl ⟨lt_of_not_ge h₀, h₁⟩)
        · exact Or.inr (Or.inr (lt_of_not_ge h₁))
    · rintro (ht | ht | ht) <;> linarith
  have hi := dampedPerronMajorant_integrableOn_Ioi hε hL
  have hi₀ : IntegrableOn (dampedPerronMajorantIntegrand ε L) s₀ :=
    hi.mono (by intro t ht; exact ht.1) le_rfl
  have hi₁ : IntegrableOn (dampedPerronMajorantIntegrand ε L) s₁ :=
    hi.mono (by intro t ht; exact zero_lt_one.trans ht.1) le_rfl
  have hi₂ : IntegrableOn (dampedPerronMajorantIntegrand ε L) s₂ :=
    hi.mono (by intro t ht; exact (inv_pos.mpr hε).trans ht) le_rfl
  have hd₁₂ : Disjoint s₁ s₂ := Set.disjoint_left.2 (by
    intro t ht₁ ht₂
    exact (not_lt_of_ge ht₁.2) ht₂)
  have hd₀ : Disjoint s₀ (s₁ ∪ s₂) := Set.disjoint_left.2 (by
    intro t ht₀ ht
    rcases ht with ht₁ | ht₂
    · exact (not_lt_of_ge ht₀.2) ht₁.1
    · exact (not_lt_of_ge (ht₀.2.trans hb)) ht₂)
  have hsplit :
      (∫ t in Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L t) =
        (∫ t in s₀, dampedPerronMajorantIntegrand ε L t) +
          (∫ t in s₁, dampedPerronMajorantIntegrand ε L t) + (∫ t in s₂, dampedPerronMajorantIntegrand ε L t) := by
    rw [hs, setIntegral_union hd₀ (measurableSet_Ioc.union measurableSet_Ioi) hi₀
      (hi₁.union hi₂), setIntegral_union hd₁₂ measurableSet_Ioi hi₁ hi₂, add_assoc]
  rw [hsplit]
  have h₀ := dampedPerronMajorant_integral_head_le hε hL
  have h₁ := dampedPerronMajorant_integral_middle_le hε hε1 hL
  have h₂ := dampedPerronMajorant_integral_tail_le_one hε hL
  change (∫ t in s₀, dampedPerronMajorantIntegrand ε L t) ≤ L at h₀
  change (∫ t in s₁, dampedPerronMajorantIntegrand ε L t) ≤ Real.log ε⁻¹ at h₁
  change (∫ t in s₂, dampedPerronMajorantIntegrand ε L t) ≤ 1 at h₂
  rw [one_div]
  linarith

end AnalyticNumberTheory.LargeSieve
