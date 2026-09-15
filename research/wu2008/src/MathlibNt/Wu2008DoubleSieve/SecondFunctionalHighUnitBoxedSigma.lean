import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitBoxedLimit

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnit
open Real Finset

/-- Original sigma occurs exactly once. -/
noncomputable def boxedSigma20 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (a2 a3 b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    boxed20 N d δ (a2 d) (a3 d) (b d)

noncomputable def boxedSigma21 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (a3 b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    boxed21 N d δ (a3 d) (b d)

/-- The original J section at the actual same phi, without a supremum. -/
noncomputable def boxedIntegral20 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (a2 a3 b : ℕ → ℝ) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) /
      ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        J20 (a2 d) (a3 d) (b d) (omega3XPhi N d δ)

noncomputable def boxedIntegral21 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (a3 b : ℕ → ℝ) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) /
      ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        J21 (a3 d) (b d) (omega3XPhi N d δ)

/-- Finite two-sided summation with the existing coefficient reciprocal mass. -/
theorem sigma_abs_error {i N : ℕ} {δ B : ℝ} (W : Fin i → Finset ℕ)
    (E J : ℕ → ℝ)
    (hError : ∀ d ∈ boxConvolutionSupport W,
      |E d - (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * J d| ≤ B / d) :
    |(∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * E d) -
      (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) /
          ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * J d| ≤
      B * boxConvolutionReciprocalMass W := by
  rw [mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W,
        |(convolutionCoeff W d : ℝ) * E d - (N : ℝ) *
          ((convolutionCoeff W d : ℝ) /
            ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * J d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, B * ((convolutionCoeff W d : ℝ) / d) := by
      apply sum_le_sum
      intro d hd
      have heq : (convolutionCoeff W d : ℝ) * E d - (N : ℝ) *
          ((convolutionCoeff W d : ℝ) /
            ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * J d) =
          (convolutionCoeff W d : ℝ) *
            (E d - (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * J d) := by ring
      rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      convert mul_le_mul_of_nonneg_left (hError d hd)
        (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _) using 1
      ring
    _ = _ := by rw [boxConvolutionReciprocalMass, mul_sum]

/-- One common threshold; windows are arbitrary functions chosen after the box.
Both individual absolute errors have the stated tolerance, not their sum. -/
theorem boxed_sigma_pair_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) →
      let W := convolutionWuWindows N Δ V
      (|boxedSigma20 N δ W a2 a3 b - boxedIntegral20 N δ W a2 a3 b| ≤
        epsilon * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) ∧
      (|boxedSigma21 N δ W a3 b - boxedIntegral21 N δ W a3 b| ≤
        epsilon * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) := by
  have hη := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT4, hT⟩ := boxed_pair_unnormalized k hδ hδhi (mul_pos he hη)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb a2 a3 b hw
  have hN2 : 2 ≤ N := by omega
  have hpoint : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (|boxed20 N d δ (a2 d) (a3 d) (b d) -
        (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          J20 (a2 d) (a3 d) (b d) (omega3XPhi N d δ)| ≤
        epsilon * ((N : ℝ) / log N) / d) ∧
      (|boxed21 N d δ (a3 d) (b d) -
        (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          J21 (a3 d) (b d) (omega3XPhi N d δ)| ≤
        epsilon * ((N : ℝ) / log N) / d) := by
    intro d hd
    obtain ⟨ha2, ha3, hb'⟩ := hw d hd
    obtain ⟨h20, h21⟩ := hT N hN i Δ V hb d hd (a2 d) (a3 d) (b d) ha2 ha3 hb'
    have hpay := omega3X_log_scale_error_le hN2 hδ hδhi hb hd he.le
    exact ⟨h20.le.trans hpay, h21.le.trans hpay⟩
  exact ⟨sigma_abs_error _ _ _ (fun d hd => (hpoint d hd).1),
    sigma_abs_error _ _ _ (fun d hd => (hpoint d hd).2)⟩

/-- Half the total budget is assigned internally to each component. The same T
supports both individual bounds and the two-sided combined envelope comparison. -/
theorem boxed_sigma_pair_combined (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) →
      let W := convolutionWuWindows N Δ V
      (|boxedSigma20 N δ W a2 a3 b - boxedIntegral20 N δ W a2 a3 b| ≤
        (epsilon / 2) * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) ∧
      (|boxedSigma21 N δ W a3 b - boxedIntegral21 N δ W a3 b| ≤
        (epsilon / 2) * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) ∧
      (|boxedSigma20 N δ W a2 a3 b + boxedSigma21 N δ W a3 b -
        (boxedIntegral20 N δ W a2 a3 b + boxedIntegral21 N δ W a3 b)| ≤
        epsilon * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) := by
  obtain ⟨T, hT4, hT⟩ := boxed_sigma_pair_uniform k hδ hδhi (half_pos he)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb a2 a3 b hw
  obtain ⟨h20, h21⟩ := hT N hN i Δ V hb a2 a3 b hw
  dsimp only at h20 h21 ⊢
  refine ⟨h20, h21, ?_⟩
  have ht := abs_add_le
    (boxedSigma20 N δ (convolutionWuWindows N Δ V) a2 a3 b -
      boxedIntegral20 N δ (convolutionWuWindows N Δ V) a2 a3 b)
    (boxedSigma21 N δ (convolutionWuWindows N Δ V) a3 b -
      boxedIntegral21 N δ (convolutionWuWindows N Δ V) a3 b)
  rw [show ∀ x y z w : ℝ, x - y + (z - w) = x + z - (y + w) by intros; ring] at ht
  linarith

end Wu2008DoubleSieve.HighUnit
