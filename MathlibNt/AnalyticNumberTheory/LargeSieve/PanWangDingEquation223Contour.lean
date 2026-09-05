import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEarlySourceReduction
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteContour

set_option maxHeartbeats 800000
noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Equation (2.8), with the original coprimality restriction. -/
def panSourceG (f : ℕ → ℂ) (m n : ℕ) : ℂ :=
  if Nat.Coprime n m then f n else 0

/-- Equations (2.2), (2.8): the prime indicator restricted by `(n,m)=1`. -/
def panSourceD (m n : ℕ) : ℂ :=
  if Nat.Coprime n m ∧ Nat.Prime n then 1 else 0

/-- The literal short polynomial (2.19). -/
def panShortF₁ {q : ℕ} (m H : ℕ) (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H, panSourceD m n * χ.1 (n : ZMod q) / (n : ℂ) ^ s

/-- Equation (2.21), including the clipped last dyadic cell. -/
def panDyadicG {q : ℕ} (f : ℕ → ℂ) (m A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  ∑ a ∈ Finset.Ioc (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂),
    panSourceG f m a * χ.1 (a : ZMod q) / (a : ℂ) ^ s

/-- The complete kernel in (2.23), not an abstract holomorphic input. -/
def pan223Kernel {q : ℕ} (f : ℕ → ℂ) (m H y A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  panDyadicG f m A₁ A₂ k χ s * panShortF₁ m H χ s * (y : ℂ) ^ s / s

theorem panFinitePolynomial_differentiable (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) :
    Differentiable ℂ (fun s : ℂ => ∑ n ∈ S, c n / (n : ℂ) ^ s) := by
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
  exact (differentiable_const _).div
    (differentiable_id.const_cpow (Or.inl hn0))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

theorem panShortF₁_differentiable {q : ℕ} (m H : ℕ) (χ : PrimitiveCharacter q) :
    Differentiable ℂ (panShortF₁ m H χ) := by
  apply panFinitePolynomial_differentiable
  intro n hn
  exact (Finset.mem_Icc.mp hn).1

theorem panDyadicG_differentiable {q : ℕ} (f : ℕ → ℂ) (m A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) : Differentiable ℂ (panDyadicG f m A₁ A₂ k χ) := by
  apply panFinitePolynomial_differentiable
  intro a ha
  exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp ha).1

theorem pan223Kernel_differentiableOn {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (hy : 0 < y) :
    DifferentiableOn ℂ (pan223Kernel f m H y A₁ A₂ k χ) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact (((panDyadicG_differentiable f m A₁ A₂ k χ s).mul
    (panShortF₁_differentiable m H χ s)).mul
    (differentiableAt_id.const_cpow (Or.inl hy0))).div
    differentiableAt_id hs0 |>.differentiableWithinAt

/-- Exact finite shift with actual `ds = i dt`. The top edge is traversed
left-to-right and the bottom edge right-to-left in the difference. -/
theorem pan223_oriented_rectangle {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (hy : 0 < y)
    {α T : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 ≤ T) :
    I * (∫ t in -T..T, chen1973VerticalSection
      (pan223Kernel f m H y A₁ A₂ k χ) α t) -
    I * (∫ t in -T..T, chen1973VerticalSection
      (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t) =
    (∫ u in (1 / 2 : ℝ)..α, pan223Kernel f m H y A₁ A₂ k χ (u + T * I)) -
    (∫ u in (1 / 2 : ℝ)..α, pan223Kernel f m H y A₁ A₂ k χ (u + (-T) * I)) := by
  have hf := (pan223Kernel_differentiableOn f m H y A₁ A₂ k χ hy).mono
    (show {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T} ⊆
      {s : ℂ | 0 < s.re} from fun s hs => by dsimp; linarith [hs.1])
  have hc := Eq21FiniteContour_rectangle_vertical_identity hα hT hf
  have hc' := congrArg (fun z : ℂ => I * z) hc
  rw [← mul_assoc, I_mul_I] at hc'
  simpa [mul_sub, chen1973HorizontalSection, sub_eq_add_neg, add_comm, mul_add] using hc'

theorem panSourceG_norm_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (m n : ℕ) :
    ‖panSourceG f m n‖ ≤ 1 := by
  unfold panSourceG
  split_ifs <;> simp [hf]

theorem panSourceD_norm_le (m n : ℕ) : ‖panSourceD m n‖ ≤ 1 := by
  unfold panSourceD
  split_ifs <;> norm_num

/-- The precise reciprocal-square-root sum in (2.23). -/
def panHalfSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹

theorem panHalfSum_eq_rpow (N : ℕ) :
    panHalfSum N = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2) : ℝ) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.sqrt_eq_rpow]

theorem panHalfSum_nonneg (N : ℕ) : 0 ≤ panHalfSum N := by
  unfold panHalfSum
  positivity

theorem panFinitePolynomial_norm_le (S : Finset ℕ) (c : ℕ → ℂ)
    (N : ℕ) (hS : S ⊆ Finset.Icc 1 N) (hc : ∀ n ∈ S, ‖c n‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∑ n ∈ S, c n / (n : ℂ) ^ s‖ ≤ panHalfSum N := by
  calc
    _ ≤ ∑ n ∈ S, ‖c n / (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by linarith
      rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      calc
        ‖c n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (hc n hn) (Real.rpow_nonneg hn0.le _)
        _ ≤ 1 / Real.sqrt n := by
          apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn0)
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hn1 hs
        _ = _ := one_div _
    _ ≤ panHalfSum N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro n _ _
      positivity

theorem panShortF₁_norm_le {q : ℕ} (m H : ℕ) (χ : PrimitiveCharacter q)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) : ‖panShortF₁ m H χ s‖ ≤ panHalfSum H := by
  apply panFinitePolynomial_norm_le _ _ H (fun _ h => h) _ s hs
  intro n _
  rw [norm_mul]
  exact mul_le_one₀ (panSourceD_norm_le m n) (norm_nonneg _) (χ.1.norm_le_one _)

theorem panDyadicG_norm_le {q : ℕ} (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) : ‖panDyadicG f m A₁ A₂ k χ s‖ ≤ panHalfSum A₂ := by
  apply panFinitePolynomial_norm_le _ _ A₂ _ _ s hs
  · intro a ha
    rcases Finset.mem_Ioc.mp ha with ⟨ha, hb⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hb.trans (min_le_right _ _)⟩
  · intro a _
    rw [norm_mul]
    exact mul_le_one₀ (panSourceG_norm_le f hf m a) (norm_nonneg _) (χ.1.norm_le_one _)

/-- Pointwise estimate on either horizontal edge, uniform in all characters
and dyadic cells. -/
theorem pan223_horizontal_pointwise {q : ℕ} (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (hy : 1 ≤ y)
    {α T u t : ℝ} (hu : 1 / 2 ≤ u) (huα : u ≤ α) (hT : 0 < T) (ht : |t| = T) :
    ‖pan223Kernel f m H y A₁ A₂ k χ (u + t * I)‖ ≤
      (y : ℝ) ^ α / T * panHalfSum H * panHalfSum A₂ := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hs : ((u : ℂ) + t * I).re = u := by simp
  have hn : T ≤ ‖(u : ℂ) + t * I‖ := by
    simpa [ht] using Complex.abs_im_le_norm ((u : ℂ) + t * I)
  have hG := panDyadicG_norm_le f hf m A₁ A₂ k χ (u + t * I) (by simpa using hu)
  have hF := panShortF₁_norm_le m H χ (u + t * I) (by simpa using hu)
  have hHN := panHalfSum_nonneg H
  have hAN := panHalfSum_nonneg A₂
  unfold pan223Kernel
  rw [norm_div, norm_mul, norm_mul, show (y : ℂ) = ((y : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0, hs]
  calc
    _ ≤ (panHalfSum A₂ * panHalfSum H * (y : ℝ) ^ α) / T := by
      apply div_le_div₀ (by positivity)
      · apply mul_le_mul
        · exact mul_le_mul hG hF (norm_nonneg _) (panHalfSum_nonneg _)
        · exact Real.rpow_le_rpow_of_exponent_le hy1 huα
        · positivity
        · positivity
      · exact hT
      · exact hn
    _ = _ := by ring

/-- Both vertical sections are genuine finite integrals. -/
theorem pan223_vertical_integrable {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (hy : 0 < y)
    {α T v : ℝ} (hT : 0 ≤ T) (hv : v ∈ Icc (1 / 2) α) :
    IntervalIntegrable (chen1973VerticalSection (pan223Kernel f m H y A₁ A₂ k χ) v)
      volume (-T) T := by
  apply Eq21FiniteContour_vertical_intervalIntegrable hT hv
  apply (pan223Kernel_differentiableOn f m H y A₁ A₂ k χ hy).continuousOn.mono
  intro s hs
  dsimp at hs ⊢
  linarith [hs.1]

/-- Both horizontal integrals exist independently of the contour identity. -/
theorem pan223_horizontal_integrable {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (hy : 0 < y)
    {α t : ℝ} (hα : 1 / 2 ≤ α) :
    IntervalIntegrable (fun u : ℝ => pan223Kernel f m H y A₁ A₂ k χ (u + t * I))
      volume (1 / 2) α := by
  apply Eq21FiniteContour_horizontal_intervalIntegrable hα (le_refl |t|)
  apply (pan223Kernel_differentiableOn f m H y A₁ A₂ k χ hy).continuousOn.mono
  intro s hs
  dsimp at hs ⊢
  linarith [hs.1]

/-- Each horizontal edge separately has the original half-sum bound. -/
theorem pan223_horizontal_integral_bound {q : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hy : 1 ≤ y) {α T t : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 < T) (ht : |t| = T) :
    ‖∫ u in (1 / 2 : ℝ)..α, pan223Kernel f m H y A₁ A₂ k χ (u + t * I)‖ ≤
      ((y : ℝ) ^ α / T * panHalfSum H * panHalfSum A₂) * (α - 1 / 2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := α)
    (f := fun u : ℝ => pan223Kernel f m H y A₁ A₂ k χ (u + t * I))
    (C := (y : ℝ) ^ α / T * panHalfSum H * panHalfSum A₂) (by
      intro u hu
      rw [uIoc_of_le hα] at hu
      exact pan223_horizontal_pointwise f hf m H y A₁ A₂ k χ hy hu.1.le hu.2 hT ht)
  rw [abs_of_nonneg (sub_nonneg.mpr hα)] at h
  exact h

/-- Finite-shift bound, retaining exactly the half-sums displayed in (2.23). -/
theorem pan223_finite_shift_bound {q : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hy : 1 ≤ y) {α T : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 < T) :
    ‖I * (∫ t in -T..T, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) α t) -
      I * (∫ t in -T..T, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t)‖ ≤
      2 * (α - 1 / 2) * (y : ℝ) ^ α / T * panHalfSum H * panHalfSum A₂ := by
  rw [pan223_oriented_rectangle f m H y A₁ A₂ k χ hy hα hT.le]
  have ht := pan223_horizontal_integral_bound f hf m H y A₁ A₂ k χ hy hα hT
    (show |T| = T from abs_of_pos hT)
  have hb := pan223_horizontal_integral_bound f hf m H y A₁ A₂ k χ hy hα hT
    (show |-T| = T by simp [abs_of_pos hT])
  simp only [Complex.ofReal_neg] at hb
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add ht hb
    _ = 2 * (α - 1 / 2) * (y : ℝ) ^ α / T * panHalfSum H * panHalfSum A₂ := by ring


end AnalyticNumberTheory.LargeSieve