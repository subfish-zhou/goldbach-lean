import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateIntegral

/-! # Literal Gamma10/Gamma13 integrals, with a fixed inner gate -/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

noncomputable def fourthRowTripleGatedStart (ten : Bool) : ℝ := if ten then 25 / 89 else 25 / 103
noncomputable def fourthRowTripleGatedStop (ten : Bool) : ℝ := if ten then 100 / 291 else 25 / 89
noncomputable def fourthRowTripleGatedMiddleStart (ten : Bool) (t : ℝ) : ℝ := if ten then t else 25 / 89

noncomputable def fourthRowTripleGatedInner (f : ℝ → ℝ → ℝ → ℝ) (t u : ℝ) : ℝ :=
  ∫ v in (100 / 291 : ℝ)..(2 / 5), f t u v / v

noncomputable def fourthRowTripleGatedMiddle (ten : Bool) (f : ℝ → ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in fourthRowTripleGatedMiddleStart ten t..(100 / 291), fourthRowTripleGatedInner f t u / u

noncomputable def fourthRowTripleGatedIntegral (ten : Bool) (φ : ℝ) : ℝ :=
  ∫ t in fourthRowTripleGatedStart ten..fourthRowTripleGatedStop ten,
    ∫ u in fourthRowTripleGatedMiddleStart ten t..(100 / 291),
      ∫ v in (100 / 291 : ℝ)..(2 / 5), buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v)

noncomputable def fourthRowTripleGatedEnvelope (ten : Bool) : ℝ :=
  sSup (fourthRowTripleGatedIntegral ten '' Ici 2)

theorem fourthRowTripleGated_endpoints (ten : Bool) :
    1 / 10 ≤ fourthRowTripleGatedStart ten ∧
      fourthRowTripleGatedStart ten ≤ fourthRowTripleGatedStop ten ∧
      fourthRowTripleGatedStop ten ≤ 100 / 291 := by
  cases ten <;> norm_num [fourthRowTripleGatedStart, fourthRowTripleGatedStop]

theorem fourthRowTripleGated_middle_endpoints (ten : Bool) {t : ℝ}
    (ht : t ∈ Icc (fourthRowTripleGatedStart ten) (fourthRowTripleGatedStop ten)) :
    1 / 10 ≤ fourthRowTripleGatedMiddleStart ten t ∧
      fourthRowTripleGatedMiddleStart ten t ≤ 100 / 291 := by
  cases ten
  · norm_num [fourthRowTripleGatedMiddleStart]
  · exact ⟨(fourthRowTripleGated_endpoints true).1.trans ht.1,
      ht.2.trans (fourthRowTripleGated_endpoints true).2.2⟩

theorem fourthRowTripleGated_inner_regular {f : ℝ → ℝ → ℝ → ℝ} {M K : ℝ}
    (hw : PrimeOrderedWeight M K f) (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ u ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |fourthRowTripleGatedInner f t u| ≤ 4 * M) ∧
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ t' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ u ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |fourthRowTripleGatedInner f t u - fourthRowTripleGatedInner f t' u| ≤ 4 * K * |t - t'|) ∧
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ u ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ u' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |fourthRowTripleGatedInner f t u - fourthRowTripleGatedInner f t u'| ≤ 4 * K * |u - u'|) := by
  have hc t ht u hu := primeOrdered_continuous_of_lipschitz (hw.third t ht u hu)
  refine ⟨fun t ht u hu => primeOrdered_integral_norm_le_four (by norm_num) (by norm_num) hM
    (hw.bound t ht u hu), ?_, ?_⟩
  · intro t ht t' ht' u hu
    exact (primeOrdered_integral_sub_bound (hc t ht u hu) (hc t' ht' u hu)
      (by norm_num) (by norm_num) (mul_nonneg hK (abs_nonneg _))
      (hw.first t ht t' ht' u hu)).trans_eq (by ring)
  · intro t ht u hu u' hu'
    exact (primeOrdered_integral_sub_bound (hc t ht u hu) (hc t ht u' hu')
      (by norm_num) (by norm_num) (mul_nonneg hK (abs_nonneg _))
      (hw.second t ht u hu u' hu')).trans_eq (by ring)

theorem fourthRowTripleGated_middle_regular {f : ℝ → ℝ → ℝ → ℝ} {M K : ℝ}
    (hw : PrimeOrderedWeight M K f) (hM : 0 ≤ M) (hK : 0 ≤ K) (ten : Bool) :
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |fourthRowTripleGatedMiddle ten f t| ≤ 16 * M) ∧
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ t' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |fourthRowTripleGatedMiddle ten f t - fourthRowTripleGatedMiddle ten f t'| ≤
        (16 * K + 40 * M) * |t - t'|) := by
  obtain ⟨hb, ht, hu⟩ := fourthRowTripleGated_inner_regular hw hM hK
  have hc t hm := primeOrdered_continuous_of_lipschitz (hu t hm)
  cases ten
  · refine ⟨fun t hm => ?_, fun t hm t' hm' => ?_⟩
    · exact (primeOrdered_integral_norm_le_four (by norm_num [fourthRowTripleGatedMiddleStart]) (by norm_num)
        (by positivity : 0 ≤ 4 * M) (hb t hm)).trans_eq (by ring)
    · have h := primeOrdered_integral_sub_bound (hc t hm) (hc t' hm')
        (by norm_num : (25 / 89 : ℝ) ∈ Icc (1 / 10) (1 / 2))
        (by norm_num : (100 / 291 : ℝ) ∈ Icc (1 / 10) (1 / 2))
        (by positivity : 0 ≤ 4 * K * |t - t'|) (fun u hu' => ht t hm t' hm' u hu')
      exact h.trans (by nlinarith [mul_nonneg hM (abs_nonneg (t - t'))])
  · have h := primeOrdered_moving_integral_lipschitz
      (by norm_num : (100 / 291 : ℝ) ∈ Icc (1 / 10) (1 / 2))
      (by positivity : 0 ≤ 4 * M) (by positivity : 0 ≤ 4 * K) hc hb ht
    simpa only [fourthRowTripleGatedMiddle, fourthRowTripleGatedMiddleStart, if_true,
      show (4 * (4 * M) : ℝ) = 16 * M by ring,
      show (4 * (4 * K) + 10 * (4 * M) : ℝ) = 16 * K + 40 * M by ring] using h

theorem fourthRowTripleGated_inner_eq (φ t u : ℝ) :
    (∫ v in (100 / 291 : ℝ)..(2 / 5), buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v)) =
      fourthRowTripleGatedInner (primeOrderedBuchstabWeight φ) t u / u / t := by
  unfold fourthRowTripleGatedInner primeOrderedBuchstabWeight
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div]
  congr 1
  funext v
  ring

theorem fourthRowTripleGated_integral_eq (ten : Bool) (φ : ℝ) :
    fourthRowTripleGatedIntegral ten φ =
      ∫ t in fourthRowTripleGatedStart ten..fourthRowTripleGatedStop ten,
        fourthRowTripleGatedMiddle ten (primeOrderedBuchstabWeight φ) t / t := by
  unfold fourthRowTripleGatedIntegral fourthRowTripleGatedMiddle
  simp_rw [fourthRowTripleGated_inner_eq, intervalIntegral.integral_div]

theorem fourthRowTripleGated_integrable (ten : Bool) {φ : ℝ} (hφ : 2 ≤ φ) :
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ u ∈ Icc (1 / 10 : ℝ) (1 / 2),
      IntervalIntegrable (fun v => buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v))
        volume (100 / 291) (2 / 5)) ∧
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2),
      IntervalIntegrable (fun u => ∫ v in (100 / 291 : ℝ)..(2 / 5),
        buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v))
        volume (fourthRowTripleGatedMiddleStart ten t) (100 / 291)) ∧
    IntervalIntegrable (fun t => ∫ u in fourthRowTripleGatedMiddleStart ten t..(100 / 291),
      ∫ v in (100 / 291 : ℝ)..(2 / 5), buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v))
        volume (fourthRowTripleGatedStart ten) (fourthRowTripleGatedStop ten) := by
  have hK : 0 ≤ 1000 * φ + 200 := by linarith
  have hw := primeOrdered_buchstab_weight hφ (le_refl φ)
  have hi := fourthRowTripleGated_inner_regular hw (by norm_num) hK
  have hm := fourthRowTripleGated_middle_regular hw (by norm_num) hK ten
  refine ⟨?_, ?_, ?_⟩
  · intro t ht u hu
    have h := ((primeOrdered_integrable
      (primeOrdered_continuous_of_lipschitz (hw.third t ht u hu))
      (by norm_num : (100 / 291 : ℝ) ∈ Icc (1 / 10) (1 / 2))
      (by norm_num : (2 / 5 : ℝ) ∈ Icc (1 / 10) (1 / 2))).div_const u).div_const t
    convert h using 1
    funext v
    unfold primeOrderedBuchstabWeight
    ring
  · intro t ht
    simp_rw [fourthRowTripleGated_inner_eq]
    apply (primeOrdered_integrable (primeOrdered_continuous_of_lipschitz (hi.2.2 t ht))
      ?_ (by norm_num)).div_const t
    cases ten
    · norm_num [fourthRowTripleGatedMiddleStart]
    · exact ht
  · have he := fourthRowTripleGated_endpoints ten
    simp_rw [fourthRowTripleGated_inner_eq, intervalIntegral.integral_div]
    exact primeOrdered_integrable (primeOrdered_continuous_of_lipschitz hm.2)
      ⟨he.1, by linarith [he.2.1, he.2.2]⟩
      ⟨he.1.trans he.2.1, by linarith [he.2.2]⟩

theorem fourthRowTripleGated_integral_bounds (ten : Bool) {φ : ℝ} (hφ : 2 ≤ φ) :
    0 ≤ fourthRowTripleGatedIntegral ten φ ∧ fourthRowTripleGatedIntegral ten φ ≤ 640 := by
  have he := fourthRowTripleGated_endpoints ten
  constructor
  · unfold fourthRowTripleGatedIntegral
    apply intervalIntegral.integral_nonneg he.2.1
    intro t ht
    have hm := fourthRowTripleGated_middle_endpoints ten ht
    apply intervalIntegral.integral_nonneg hm.2
    intro u hu
    apply intervalIntegral.integral_nonneg (by norm_num : (100 / 291 : ℝ) ≤ 2 / 5)
    intro v hv
    exact (omega3XIntegralKernel_bounds hφ
      ⟨he.1.trans ht.1, by linarith [ht.2, he.2.2]⟩
      ⟨hm.1.trans hu.1, by linarith [hu.2]⟩
      ⟨by linarith [hv.1], by linarith [hv.2]⟩).1
  · rw [fourthRowTripleGated_integral_eq]
    have hm := fourthRowTripleGated_middle_regular (primeOrdered_buchstab_weight hφ (le_refl φ))
      (by norm_num) (by linarith : 0 ≤ 1000 * φ + 200) ten
    have hh := primeOrdered_integral_norm_le_four
      ⟨he.1, by linarith [he.2.1, he.2.2]⟩
      ⟨he.1.trans he.2.1, by linarith [he.2.2]⟩ (by norm_num : (0 : ℝ) ≤ 16 * 10) hm.1
    norm_num only [show (4 * (16 * 10) : ℝ) = 640 by norm_num] at hh
    exact (le_abs_self _).trans hh

theorem fourthRowTripleGated_image_nonempty (ten : Bool) :
    (fourthRowTripleGatedIntegral ten '' Ici 2).Nonempty :=
  ⟨_, mem_image_of_mem _ (show (2 : ℝ) ∈ Ici 2 by simp)⟩

theorem fourthRowTripleGated_image_bounded (ten : Bool) :
    BddAbove (fourthRowTripleGatedIntegral ten '' Ici 2) := by
  refine ⟨640, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact (fourthRowTripleGated_integral_bounds ten hφ).2

theorem fourthRowTripleGated_le_envelope (ten : Bool) {φ : ℝ} (hφ : 2 ≤ φ) :
    fourthRowTripleGatedIntegral ten φ ≤ fourthRowTripleGatedEnvelope ten :=
  le_csSup (fourthRowTripleGated_image_bounded ten) (mem_image_of_mem _ hφ)

theorem fourthRowTripleGated_envelope_bounds (ten : Bool) :
    0 ≤ fourthRowTripleGatedEnvelope ten ∧ fourthRowTripleGatedEnvelope ten ≤ 640 := by
  refine ⟨((fourthRowTripleGated_integral_bounds ten (le_refl 2)).1).trans
    (fourthRowTripleGated_le_envelope ten (le_refl 2)), ?_⟩
  apply csSup_le (fourthRowTripleGated_image_nonempty ten)
  rintro _ ⟨φ, hφ, rfl⟩
  exact (fourthRowTripleGated_integral_bounds ten hφ).2

end Wu2008DoubleSieve
