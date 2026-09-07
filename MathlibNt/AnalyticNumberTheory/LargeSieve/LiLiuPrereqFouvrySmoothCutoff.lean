import Mathlib

/-!
# A fixed smooth dyadic cutoff

The bump is chosen once, independently of every scale and Fourier frequency.
Its outer radius is one around `3 / 2`, so its support is even smaller than
the interval `[1 / 2, 3]` required for dyadic smoothing.
-/

noncomputable section

open Set
open scoped ContDiff SchwartzMap FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Fixed inner and outer radii; there is no scale-dependent choice of bump. -/
def dyadicBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The real-valued fixed cutoff. -/
def dyadicCutoff (x : ℝ) : ℝ := dyadicBump x

theorem dyadicCutoff_contDiff : ContDiff ℝ ∞ dyadicCutoff :=
  dyadicBump.contDiff

theorem dyadicCutoff_nonneg (x : ℝ) : 0 ≤ dyadicCutoff x :=
  dyadicBump.nonneg

theorem dyadicCutoff_le_one (x : ℝ) : dyadicCutoff x ≤ 1 :=
  dyadicBump.le_one

theorem dyadicCutoff_eq_one {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    dyadicCutoff x = 1 := by
  apply dyadicBump.one_of_mem_closedBall
  change |x - 3 / 2| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem dyadicCutoff_tsupport_subset :
    tsupport dyadicCutoff ⊆ Icc (1 / 2 : ℝ) 3 := by
  change tsupport (dyadicBump : ℝ → ℝ) ⊆ _
  rw [dyadicBump.tsupport_eq]
  intro x hx
  change |x - 3 / 2| ≤ 1 at hx
  obtain ⟨h₁, h₂⟩ := abs_le.mp hx
  constructor <;> linarith

theorem dyadicCutoff_hasCompactSupport : HasCompactSupport dyadicCutoff :=
  dyadicBump.hasCompactSupport

/-- Dilation of the same fixed cutoff, not a newly chosen bump. -/
def scaledDyadicCutoff (M x : ℝ) : ℝ := dyadicCutoff (x / M)

theorem scaledDyadicCutoff_contDiff (M : ℝ) :
    ContDiff ℝ ∞ (scaledDyadicCutoff M) :=
  dyadicCutoff_contDiff.comp (contDiff_id.div_const M)

theorem scaledDyadicCutoff_nonneg (M x : ℝ) : 0 ≤ scaledDyadicCutoff M x :=
  dyadicCutoff_nonneg _

theorem scaledDyadicCutoff_le_one (M x : ℝ) : scaledDyadicCutoff M x ≤ 1 :=
  dyadicCutoff_le_one _

theorem scaledDyadicCutoff_eq_one {M x : ℝ} (hM : 0 < M)
    (hx : x ∈ Icc M (2 * M)) : scaledDyadicCutoff M x = 1 := by
  apply dyadicCutoff_eq_one
  exact ⟨(le_div_iff₀ hM).mpr (by simpa using hx.1),
    (div_le_iff₀ hM).mpr hx.2⟩

theorem scaledDyadicCutoff_tsupport_subset {M : ℝ} (hM : 0 < M) :
    tsupport (scaledDyadicCutoff M) ⊆ Icc (M / 2) (3 * M) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx' : x / M ∈ tsupport dyadicCutoff :=
    subset_closure (show x / M ∈ Function.support dyadicCutoff from hx)
  obtain ⟨h₁, h₂⟩ := dyadicCutoff_tsupport_subset hx'
  constructor
  · have := (le_div_iff₀ hM).mp h₁
    linarith
  · exact (div_le_iff₀ hM).mp h₂

theorem scaledDyadicCutoff_hasCompactSupport {M : ℝ} (hM : 0 < M) :
    HasCompactSupport (scaledDyadicCutoff M) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (scaledDyadicCutoff_tsupport_subset hM)

/-- The complex-valued Schwartz function used with Mathlib's Fourier transform. -/
def dyadicCutoffSchwartz : 𝓢(ℝ, ℂ) :=
  (dyadicCutoff_hasCompactSupport.comp_left
    (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
      (by exact Complex.ofRealCLM.contDiff.comp dyadicCutoff_contDiff)

@[simp]
theorem dyadicCutoffSchwartz_apply (x : ℝ) :
    dyadicCutoffSchwartz x = (dyadicCutoff x : ℂ) := rfl

/-- The dilation is also a genuine Schwartz function at every positive scale. -/
def scaledDyadicCutoffSchwartz (M : ℝ) (hM : 0 < M) : 𝓢(ℝ, ℂ) :=
  ((scaledDyadicCutoff_hasCompactSupport hM).comp_left
    (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (scaledDyadicCutoff_contDiff M))

@[simp]
theorem scaledDyadicCutoffSchwartz_apply (M : ℝ) (hM : 0 < M) (x : ℝ) :
    scaledDyadicCutoffSchwartz M hM x = (scaledDyadicCutoff M x : ℂ) := rfl

/-- Fourier normalization is Mathlib's `exp (-2 * π * I * x * w)`. -/
theorem scaledDyadicCutoff_fourier {M : ℝ} (hM : 0 < M) (w : ℝ) :
    𝓕 (fun x ↦ (scaledDyadicCutoff M x : ℂ)) w =
      M • (𝓕 dyadicCutoffSchwartz) (M * w) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq, Real.fourier_real_eq]
  have hphase (x : ℝ) : x / M * (M * w) = x * w := by
    field_simp
  calc
    _ = ∫ x : ℝ, Real.fourierChar (-(x / M * (M * w))) •
        dyadicCutoffSchwartz (x / M) := by
      simp only [hphase, dyadicCutoffSchwartz_apply, scaledDyadicCutoff]
    _ = |M| • ∫ x : ℝ, Real.fourierChar (-(x * (M * w))) •
        dyadicCutoffSchwartz x :=
      MeasureTheory.Measure.integral_comp_div
        (fun x : ℝ ↦ Real.fourierChar (-(x * (M * w))) • dyadicCutoffSchwartz x) M
    _ = _ := by rw [abs_of_pos hM]

/-- A global rapid-decay bound, including frequency zero. -/
theorem schwartz_norm_le_rapidDecay (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ k := by
  let B : ℝ := 2 ^ k *
    (Finset.Iic (k, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + 1, by linarith, fun x ↦ ?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f x
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  change (1 + |x|) ^ k * ‖f x‖ ≤ B at h
  nlinarith

/-- The constant is chosen before both the positive scale and the frequency. -/
theorem scaledDyadicCutoff_fourier_rapidDecay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ w : ℝ,
      ‖𝓕 (fun x ↦ (scaledDyadicCutoff M x : ℂ)) w‖ ≤
        C * M / (1 + |M * w|) ^ k := by
  obtain ⟨C, hC, hbound⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) k
  refine ⟨C, hC, fun M hM w ↦ ?_⟩
  rw [scaledDyadicCutoff_fourier hM, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * (C / (1 + |M * w|) ^ k) :=
      mul_le_mul_of_nonneg_left (hbound (M * w)) hM.le
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
