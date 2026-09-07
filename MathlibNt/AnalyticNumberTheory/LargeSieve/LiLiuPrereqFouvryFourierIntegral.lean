import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWZeroMode

/-!
# Removing the Fourier transform from a finite W sum

This is the analytic integral-to-maximum step underlying Fouvry (1987),
p. 627, (3.10)--(3.12), before the modulus and frequency decompositions.
Mathlib's Fourier transform has kernel `e(-x h / lcm(q,r))`; the CRT
factor is the positive character `fourier h (productCRTResidue / lcm)`.
Thus the frequency is the integer already used by `wPoissonFrequency`;
no extra factor `a` is inserted into its Fourier kernel. The source's
subsequent phase coordinates require a separate arithmetic identification.

The finite exponential sum retains all signed coefficients and all CRT
phases. The maximum is constructed on the actual support interval, rather
than postulated as an analytic hypothesis. No distribution estimate is proved.
-/

noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The previously defined Fourier mass is the real integral of the cutoff. -/
theorem dyadicCutoffMass_eq_integral :
    dyadicCutoffMass = ∫ x : ℝ, dyadicCutoff x := by
  unfold dyadicCutoffMass
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp [dyadicCutoffSchwartz_apply, integral_complex_ofReal]

/-- Exact mass after dilation in the original real variable. -/
theorem scaledDyadicCutoff_integral {M : ℝ} (hM : 0 < M) :
    (∫ x : ℝ, scaledDyadicCutoff M x) = M * dyadicCutoffMass := by
  simpa only [scaledDyadicCutoff, abs_of_pos hM, smul_eq_mul,
    ← dyadicCutoffMass_eq_integral] using
    (Measure.integral_comp_div dyadicCutoff M)

theorem dyadicCutoffMass_nonneg : 0 ≤ dyadicCutoffMass := by
  rw [dyadicCutoffMass_eq_integral]
  exact integral_nonneg dyadicCutoff_nonneg

/-- A numerical mass bound, obtained from the cutoff's actual support and
pointwise bound, with no Fourier or distribution estimate. -/
theorem dyadicCutoffMass_le_three : dyadicCutoffMass ≤ 3 := by
  have he : (∫ x in Icc (1 / 2 : ℝ) 3, dyadicCutoff x) = dyadicCutoffMass := by
    rw [dyadicCutoffMass_eq_integral]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hn
    exact hx (dyadicCutoff_tsupport_subset (subset_closure hn))
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc (1 / 2 : ℝ) 3) (C := 1)
    isCompact_Icc.measure_lt_top
    (fun x _ ↦ show ‖dyadicCutoff x‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg (dyadicCutoff_nonneg x)]
      exact dyadicCutoff_le_one x)
  rw [he, Real.norm_eq_abs, abs_of_nonneg dyadicCutoffMass_nonneg] at hb
  norm_num [Real.volume_real_Icc] at hb
  linarith

theorem scaledDyadicCutoff_integral_le_three_mul {M : ℝ} (hM : 0 < M) :
    (∫ x : ℝ, scaledDyadicCutoff M x) ≤ 3 * M := by
  rw [scaledDyadicCutoff_integral hM, mul_comm 3 M]
  exact mul_le_mul_of_nonneg_left dyadicCutoffMass_le_three hM.le

/-- Continuous exponential sums can be integrated against the scaled cutoff. -/
theorem scaledDyadicCutoff_mul_integrable {M : ℝ} (hM : 0 < M)
    {F : ℝ → ℂ} (hF : Continuous F) :
    Integrable (fun x ↦ (scaledDyadicCutoff M x : ℂ) * F x) := by
  have hc : Continuous (fun x ↦ (scaledDyadicCutoff M x : ℂ)) :=
    Complex.continuous_ofReal.comp (scaledDyadicCutoff_contDiff M).continuous
  have hs : HasCompactSupport (fun x ↦ (scaledDyadicCutoff M x : ℂ)) :=
    (scaledDyadicCutoff_hasCompactSupport hM).comp_left
      (g := Complex.ofRealCLM) (map_zero _)
  exact (hc.mul hF).integrable_of_hasCompactSupport hs.mul_right

/-- The reciprocal modulus and actual CRT phase, with the negative Fourier
kernel at the original real variable. There is no triangle inequality here. -/
def wFourierExponential (a : ℤ) (q r n₁ n₂ : ℕ) (h : ℤ) (x : ℝ) : ℂ :=
  (((q.lcm r : ℝ)⁻¹ : ℝ) : ℂ) *
    (Real.fourierChar (-(x * ((h : ℝ) / (q.lcm r : ℝ)))) : ℂ) *
    fourier h ((productCRTResidue q r n₁ n₂ a : ℝ) / (q.lcm r : ℝ) : UnitAddCircle)

theorem wFourierExponential_continuous
    (a : ℤ) (q r n₁ n₂ : ℕ) (h : ℤ) :
    Continuous (wFourierExponential a q r n₁ n₂ h) := by
  unfold wFourierExponential
  fun_prop

/-- Exact real integral formula for each nonzero Poisson frequency.
It even holds for zero moduli under Lean's totalized reciprocal convention. -/
theorem wPoissonFrequency_eq_integral {M : ℝ} (hM : 0 < M)
    (a : ℤ) (q r n₁ n₂ : ℕ) {h : ℤ} (hh : h ≠ 0) :
    wPoissonFrequency M a q r n₁ n₂ h =
      ∫ x : ℝ, (scaledDyadicCutoff M x : ℂ) *
        wFourierExponential a q r n₁ n₂ h x := by
  unfold wPoissonFrequency dyadicCutoffPoissonRemainder
  rw [if_neg hh]
  have hfreq : M / (q.lcm r : ℝ) * (h : ℝ) =
      M * ((h : ℝ) / (q.lcm r : ℝ)) := by ring
  rw [hfreq]
  have hscale := scaledDyadicCutoff_fourier hM ((h : ℝ) / (q.lcm r : ℝ))
  have he :
      (M / (q.lcm r : ℝ)) • (𝓕 dyadicCutoffSchwartz)
          (M * ((h : ℝ) / (q.lcm r : ℝ))) =
        (q.lcm r : ℝ)⁻¹ •
          𝓕 (fun x ↦ (scaledDyadicCutoff M x : ℂ)) ((h : ℝ) / (q.lcm r : ℝ)) := by
    rw [hscale, smul_smul]
    congr 1
    ring
  rw [he, Real.fourier_real_eq, ← integral_smul, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [wFourierExponential, Circle.smul_def, smul_eq_mul, Complex.real_smul]
  ring

/-- A finite exponential sum with its real signed coefficients still inside. -/
def wFourierExponentialSum {ι : Type*} (T : Finset ι) (A : ι → ℝ)
    (a : ℤ) (q r n₁ n₂ : ι → ℕ) (h : ι → ℤ) (x : ℝ) : ℂ :=
  ∑ i ∈ T, (A i : ℂ) * wFourierExponential a (q i) (r i) (n₁ i) (n₂ i) (h i) x

theorem wFourierExponentialSum_continuous {ι : Type*} (T : Finset ι)
    (A : ι → ℝ) (a : ℤ) (q r n₁ n₂ : ι → ℕ) (h : ι → ℤ) :
    Continuous (wFourierExponentialSum T A a q r n₁ n₂ h) := by
  unfold wFourierExponentialSum
  exact continuous_finsetSum T fun i _ ↦
    continuous_const.mul (wFourierExponential_continuous a (q i) (r i) (n₁ i) (n₂ i) (h i))

/-- Exact finite-sum integral identity, not a sum of termwise absolute values. -/
theorem sum_wPoissonFrequency_eq_integral {ι : Type*} {M : ℝ} (hM : 0 < M)
    (T : Finset ι) (A : ι → ℝ) (a : ℤ) (q r n₁ n₂ : ι → ℕ)
    (h : ι → ℤ) (hh : ∀ i ∈ T, h i ≠ 0) :
    (∑ i ∈ T, (A i : ℂ) * wPoissonFrequency M a (q i) (r i) (n₁ i) (n₂ i) (h i)) =
      ∫ x : ℝ, (scaledDyadicCutoff M x : ℂ) *
        wFourierExponentialSum T A a q r n₁ n₂ h x := by
  classical
  unfold wFourierExponentialSum
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum T]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [wPoissonFrequency_eq_integral hM a _ _ _ _ (hh i hi), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · intro i _
    exact scaledDyadicCutoff_mul_integrable hM
      (continuous_const.mul (wFourierExponential_continuous a (q i) (r i) (n₁ i) (n₂ i) (h i)))

/-- Integral majorization only uses a bound on the actual cutoff support.
The function need not have constant sign, or even be continuous. -/
theorem norm_scaledDyadicCutoff_integral_le {M : ℝ} (hM : 0 < M)
    (F : ℝ → ℂ) (B : ℝ)
    (hB : ∀ x ∈ Icc (M / 2) (3 * M), ‖F x‖ ≤ B) :
    ‖∫ x : ℝ, (scaledDyadicCutoff M x : ℂ) * F x‖ ≤
      (M * dyadicCutoffMass) * B := by
  have hint : Integrable (scaledDyadicCutoff M) :=
    (scaledDyadicCutoff_contDiff M).continuous.integrable_of_hasCompactSupport
      (scaledDyadicCutoff_hasCompactSupport hM)
  calc
    _ ≤ ∫ x : ℝ, scaledDyadicCutoff M x * B := by
      apply norm_integral_le_of_norm_le (hint.mul_const B)
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (scaledDyadicCutoff_nonneg M x)]
      by_cases hx : scaledDyadicCutoff M x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left
          (hB x (scaledDyadicCutoff_mem_Icc_of_ne_zero hM hx))
          (scaledDyadicCutoff_nonneg M x)
    _ = _ := by rw [integral_mul_const, scaledDyadicCutoff_integral hM]

/-- A pointwise exponential-sum bound may be inserted without destroying
cancellation among the real signed coefficients. -/
theorem norm_sum_wPoissonFrequency_le {ι : Type*} {M : ℝ} (hM : 0 < M)
    (T : Finset ι) (A : ι → ℝ) (a : ℤ) (q r n₁ n₂ : ι → ℕ)
    (h : ι → ℤ) (hh : ∀ i ∈ T, h i ≠ 0) (B : ℝ)
    (hB : ∀ x ∈ Icc (M / 2) (3 * M),
      ‖wFourierExponentialSum T A a q r n₁ n₂ h x‖ ≤ B) :
    ‖∑ i ∈ T, (A i : ℂ) * wPoissonFrequency M a (q i) (r i) (n₁ i) (n₂ i) (h i)‖ ≤
      (M * dyadicCutoffMass) * B := by
  rw [sum_wPoissonFrequency_eq_integral hM T A a q r n₁ n₂ h hh]
  exact norm_scaledDyadicCutoff_integral_le hM _ B hB

/-- The actual supremum of the explicit exponential sum on the support
interval. Its finiteness and attainment are proved below. -/
def wFourierExponentialSup {ι : Type*} (M : ℝ) (T : Finset ι) (A : ι → ℝ)
    (a : ℤ) (q r n₁ n₂ : ι → ℕ) (h : ι → ℤ) : ℝ :=
  sSup ((fun x ↦ ‖wFourierExponentialSum T A a q r n₁ n₂ h x‖) ''
    Icc (M / 2) (3 * M))

theorem wFourierExponentialSum_le_sup {ι : Type*} (M : ℝ) (T : Finset ι)
    (A : ι → ℝ) (a : ℤ) (q r n₁ n₂ : ι → ℕ) (h : ι → ℤ)
    {x : ℝ} (hx : x ∈ Icc (M / 2) (3 * M)) :
    ‖wFourierExponentialSum T A a q r n₁ n₂ h x‖ ≤
      wFourierExponentialSup M T A a q r n₁ n₂ h := by
  apply le_csSup
  · exact isCompact_Icc.bddAbove_image
      (wFourierExponentialSum_continuous T A a q r n₁ n₂ h).norm.continuousOn
  · exact mem_image_of_mem _ hx

theorem wFourierExponentialSup_attained {ι : Type*} {M : ℝ} (hM : 0 < M)
    (T : Finset ι) (A : ι → ℝ) (a : ℤ) (q r n₁ n₂ : ι → ℕ) (h : ι → ℤ) :
    ∃ x ∈ Icc (M / 2) (3 * M),
      wFourierExponentialSup M T A a q r n₁ n₂ h =
        ‖wFourierExponentialSum T A a q r n₁ n₂ h x‖ := by
  have hne : (Icc (M / 2) (3 * M)).Nonempty := ⟨M, by constructor <;> linarith⟩
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne
    (wFourierExponentialSum_continuous T A a q r n₁ n₂ h).norm.continuousOn
  refine ⟨x, hx, le_antisymm ?_ (wFourierExponentialSum_le_sup M T A a q r n₁ n₂ h hx)⟩
  apply csSup_le (hne.image _)
  rintro _ ⟨y, hy, rfl⟩
  exact hmax hy

/-- Unconditional analytic maximum bound for every finite signed W sum.
Arithmetic reindexing, dyadic aggregation, and distribution estimates remain
separate consumers of this theorem. -/
theorem norm_sum_wPoissonFrequency_le_sup {ι : Type*} {M : ℝ} (hM : 0 < M)
    (T : Finset ι) (A : ι → ℝ) (a : ℤ) (q r n₁ n₂ : ι → ℕ)
    (h : ι → ℤ) (hh : ∀ i ∈ T, h i ≠ 0) :
    ‖∑ i ∈ T, (A i : ℂ) * wPoissonFrequency M a (q i) (r i) (n₁ i) (n₂ i) (h i)‖ ≤
      (M * dyadicCutoffMass) * wFourierExponentialSup M T A a q r n₁ n₂ h :=
  norm_sum_wPoissonFrequency_le hM T A a q r n₁ n₂ h hh _
    (fun _ hx ↦ wFourierExponentialSum_le_sup M T A a q r n₁ n₂ h hx)

/-- The bound with numerical loss `3 * M` and an actual maximizing point
in the fixed normalized interval. The exponential sum is evaluated at `M*y`,
so its Fourier kernel is `e(-M*y*h/lcm)`, retaining every signed coefficient. -/
theorem norm_sum_wPoissonFrequency_le_three_mul_max {ι : Type*} {M : ℝ}
    (hM : 0 < M) (T : Finset ι) (A : ι → ℝ) (a : ℤ)
    (q r n₁ n₂ : ι → ℕ) (h : ι → ℤ) (hh : ∀ i ∈ T, h i ≠ 0) :
    ∃ y ∈ Icc (1 / 2 : ℝ) 3,
      (∀ z ∈ Icc (1 / 2 : ℝ) 3,
        ‖wFourierExponentialSum T A a q r n₁ n₂ h (M * z)‖ ≤
          ‖wFourierExponentialSum T A a q r n₁ n₂ h (M * y)‖) ∧
      ‖∑ i ∈ T, (A i : ℂ) * wPoissonFrequency M a (q i) (r i) (n₁ i) (n₂ i) (h i)‖ ≤
        3 * M * ‖wFourierExponentialSum T A a q r n₁ n₂ h (M * y)‖ := by
  obtain ⟨x, hx, he⟩ := wFourierExponentialSup_attained hM T A a q r n₁ n₂ h
  have hxy : M * (x / M) = x := by field_simp
  refine ⟨x / M, ⟨(le_div_iff₀ hM).mpr (by linarith [hx.1]),
    (div_le_iff₀ hM).mpr hx.2⟩, ?_, ?_⟩
  · intro z hz
    rw [hxy, ← he]
    apply wFourierExponentialSum_le_sup
    constructor <;> nlinarith [hz.1, hz.2]
  · rw [hxy]
    calc
      _ ≤ (M * dyadicCutoffMass) * ‖wFourierExponentialSum T A a q r n₁ n₂ h x‖ := by
        rw [← he]
        exact norm_sum_wPoissonFrequency_le_sup hM T A a q r n₁ n₂ h hh
      _ ≤ (M * 3) * ‖wFourierExponentialSum T A a q r n₁ n₂ h x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left dyadicCutoffMass_le_three hM.le) (norm_nonneg _)
      _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
