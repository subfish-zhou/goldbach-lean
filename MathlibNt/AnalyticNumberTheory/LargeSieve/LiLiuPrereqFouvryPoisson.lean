import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothCutoff

/-!
# Poisson extraction for the fixed dyadic cutoff

The period and the shift are arbitrary. The error constant is chosen before
the scale, period, and shift, including when the period exceeds the scale.
-/

noncomputable section

open scoped SchwartzMap FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Poisson summation on a real affine lattice, in the rescaled unit-period form. -/
theorem scaledDyadicCutoff_poisson_rescaled {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (b : ℝ) :
    (∑' z : ℤ, (scaledDyadicCutoff M (b + D * z) : ℂ)) =
      ∑' h : ℤ, (M / D) • (𝓕 dyadicCutoffSchwartz) ((M / D) * h) *
        fourier h (b / D : UnitAddCircle) := by
  have hMD : 0 < M / D := div_pos hM hD
  have hscale (z : ℤ) :
      (b / D + (z : ℝ)) / (M / D) = (b + D * z) / M := by
    field_simp
  convert (scaledDyadicCutoffSchwartz (M / D) hMD).tsum_eq_tsum_fourier (b / D)
      using 1
  · apply tsum_congr
    intro z
    simp only [scaledDyadicCutoffSchwartz_apply, scaledDyadicCutoff, hscale]
  · apply tsum_congr
    intro h
    rw [SchwartzMap.fourier_coe]
    exact congrArg (fun v : ℂ ↦ v * fourier h (b / D : UnitAddCircle))
      (scaledDyadicCutoff_fourier hMD h).symm

/-- The affine-lattice Poisson formula with the Fourier transform at `h / D`.
The positive Fourier phase is Mathlib's `fourier h (b / D)`. -/
theorem scaledDyadicCutoff_poisson {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (b : ℝ) :
    (∑' z : ℤ, (scaledDyadicCutoff M (b + D * z) : ℂ)) =
      D⁻¹ • ∑' h : ℤ,
        𝓕 (fun x ↦ (scaledDyadicCutoff M x : ℂ)) ((h : ℝ) / D) *
          fourier h (b / D : UnitAddCircle) := by
  rw [scaledDyadicCutoff_poisson_rescaled hM hD, ← tsum_const_smul'']
  apply tsum_congr
  intro h
  have hfreq : M / D * (h : ℝ) = M * ((h : ℝ) / D) := by ring
  rw [hfreq]
  simp only [scaledDyadicCutoff_fourier hM, smul_mul_assoc, smul_smul]
  congr 1
  ring

/-- A telescoping majorant that remains bounded when the mesh tends to zero. -/
theorem poisson_decay_step {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t / (1 + t * (n + 1)) ^ 2 ≤
      1 / (1 + t * n) - 1 / (1 + t * (n + 1)) := by
  have hA : 0 < 1 + t * (n : ℝ) := by positivity
  have hB : 0 < 1 + t * ((n : ℝ) + 1) := by positivity
  calc
    _ ≤ t / ((1 + t * n) * (1 + t * (n + 1))) := by
      apply div_le_div_of_nonneg_left ht.le (mul_pos hA hB)
      nlinarith
    _ = _ := by field_simp; ring

theorem poisson_decay_sum_range_le {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ n ∈ Finset.range N, t / (1 + t * ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (1 / (1 + t * (n : ℝ)) - 1 / (1 + t * ((n : ℝ) + 1))) :=
      Finset.sum_le_sum (fun n _ ↦ poisson_decay_step ht n)
    _ = 1 - 1 / (1 + t * (N : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, div_one]
        using Finset.sum_range_sub' (fun n : ℕ ↦ 1 / (1 + t * (n : ℝ))) N
    _ ≤ 1 := sub_le_self _ (by positivity)

theorem poisson_decay_summable_nat {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ ↦ t / (1 + t * ((n : ℝ) + 1)) ^ 2) :=
  summable_of_sum_range_le (fun _ ↦ by positivity) (poisson_decay_sum_range_le ht)

theorem poisson_decay_tsum_nat_le {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, t / (1 + t * ((n : ℝ) + 1)) ^ 2) ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) (poisson_decay_sum_range_le ht)

/-- The decay majorant with the main (zero-frequency) term removed. -/
def poissonNonzeroDecay (t : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 0 else t / (1 + |t * h|) ^ 2

/-- Both halves of the nonzero integer lattice have mass at most one. -/
theorem poissonNonzeroDecay_summable_tsum_le {t : ℝ} (ht : 0 < t) :
    Summable (poissonNonzeroDecay t) ∧ (∑' h : ℤ, poissonNonzeroDecay t h) ≤ 2 := by
  let a : ℕ → ℝ := fun n ↦ t / (1 + t * ((n : ℝ) + 1)) ^ 2
  have ha : Summable a := poisson_decay_summable_nat ht
  have hbound : (∑' n : ℕ, a n) ≤ 1 := poisson_decay_tsum_nat_le ht
  have hnat (n : ℕ) : poissonNonzeroDecay t ((n : ℤ) + 1) = a n := by
    have hn : (n : ℤ) + 1 ≠ 0 := by omega
    simp [poissonNonzeroDecay, hn, abs_mul, abs_of_pos ht,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), a]
  have hneg (n : ℕ) : poissonNonzeroDecay t (-((n : ℤ) + 1)) = a n := by
    simpa only [poissonNonzeroDecay, neg_eq_zero, Int.cast_neg, mul_neg, abs_neg]
      using hnat n
  have hpos : Summable (fun n : ℕ ↦ poissonNonzeroDecay t (n : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, hnat] using ha
  have hminus : Summable (fun n : ℕ ↦ poissonNonzeroDecay t (-((n : ℤ) + 1))) := by
    simpa only [hneg] using ha
  refine ⟨hpos.of_nat_of_neg_add_one hminus, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos hminus, tsum_eq_zero_add']
  · simp only [Nat.cast_zero, show poissonNonzeroDecay t 0 = 0 from rfl,
      zero_add, Nat.cast_add, Nat.cast_one, hnat, hneg]
    linarith
  · simpa only [Nat.cast_add, Nat.cast_one, hnat] using ha

/-- The nonzero-frequency part of the rescaled Poisson series. -/
def dyadicCutoffPoissonRemainder (t x : ℝ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else
    t • (𝓕 dyadicCutoffSchwartz) (t * h) * fourier h (x : UnitAddCircle)

/-- Uniform absolute control of the Fourier remainder. The same constant works
for every positive mesh and every real shift. -/
theorem dyadicCutoffPoissonRemainder_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      Summable (fun h : ℤ ↦ ‖dyadicCutoffPoissonRemainder t x h‖) ∧
        ‖∑' h : ℤ, dyadicCutoffPoissonRemainder t x h‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) 2
  refine ⟨2 * C, by positivity, fun t ht x ↦ ?_⟩
  obtain ⟨hmajor, hsum⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) :
      ‖dyadicCutoffPoissonRemainder t x h‖ ≤ C * poissonNonzeroDecay t h := by
    by_cases hh : h = 0
    · simp [dyadicCutoffPoissonRemainder, poissonNonzeroDecay, hh]
    · simp only [dyadicCutoffPoissonRemainder, poissonNonzeroDecay, if_neg hh,
        norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        fourier_apply, Circle.norm_coe, mul_one]
      calc
        _ ≤ t * (C / (1 + |t * h|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hdecay (t * h)) ht.le
        _ = _ := by ring
  have hnorm : Summable (fun h : ℤ ↦ ‖dyadicCutoffPoissonRemainder t x h‖) :=
    (hmajor.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hpoint
  refine ⟨hnorm, (norm_tsum_le_tsum_norm hnorm).trans ?_⟩
  calc
    _ ≤ ∑' h : ℤ, C * poissonNonzeroDecay t h :=
      hnorm.tsum_le_tsum hpoint (hmajor.mul_left C)
    _ = C * ∑' h : ℤ, poissonNonzeroDecay t h := tsum_mul_left
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hsum hC.le
    _ = 2 * C := by ring

/-- Exact extraction of the zero frequency from the affine-lattice formula. -/
theorem scaledDyadicCutoff_poisson_mainTerm {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (b : ℝ) :
    (∑' z : ℤ, (scaledDyadicCutoff M (b + D * z) : ℂ)) -
        (M / D) • (𝓕 dyadicCutoffSchwartz) 0 =
      ∑' h : ℤ, dyadicCutoffPoissonRemainder (M / D) (b / D) h := by
  obtain ⟨C, _, hbound⟩ := dyadicCutoffPoissonRemainder_uniform
  have hr := (hbound (M / D) (div_pos hM hD) (b / D)).1.of_norm
  let f : ℤ → ℂ := fun h ↦
    (M / D) • (𝓕 dyadicCutoffSchwartz) ((M / D) * h) *
      fourier h (b / D : UnitAddCircle)
  have hs : Summable (Function.update f 0 0) := by
    apply hr.congr
    intro h
    by_cases hh : h = 0 <;>
      simp [f, dyadicCutoffPoissonRemainder, hh]
  have heq := Summable.tsum_eq_add_tsum_ite' (f := f) 0 hs
  rw [scaledDyadicCutoff_poisson_rescaled hM hD]
  change (∑' h : ℤ, f h) - _ = _
  rw [heq]
  simp only [f, Int.cast_zero, mul_zero, fourier_zero, mul_one,
    add_sub_cancel_left, dyadicCutoffPoissonRemainder]

/-- The fixed cutoff has a universal `O(1)` progression error. In particular,
there is no restriction `D ≤ M` and the constant does not depend on the shift. -/
theorem scaledDyadicCutoff_poisson_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M D : ℝ, 0 < M → 0 < D → ∀ b : ℝ,
      ‖(∑' z : ℤ, (scaledDyadicCutoff M (b + D * z) : ℂ)) -
          (M / D) • (𝓕 dyadicCutoffSchwartz) 0‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := dyadicCutoffPoissonRemainder_uniform
  refine ⟨C, hC, fun M D hM hD b ↦ ?_⟩
  rw [scaledDyadicCutoff_poisson_mainTerm hM hD]
  exact (hbound (M / D) (div_pos hM hD) (b / D)).2

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
