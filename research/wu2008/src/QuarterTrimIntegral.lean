import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open Set MeasureTheory

namespace QuarterTrim

noncomputable def alpha : ℝ := 100 / 1327
noncomputable def d : ℝ := 1 / 4 - 3 * alpha
noncomputable def q : ℝ := 211041 / 10000000
noncomputable def top (x : ℝ) : ℝ := 1 / 2 - 2 * alpha - x
noncomputable def u (x y : ℝ) : ℝ := (1 / 2 - x - y) / alpha
noncomputable def kernel (p : ℝ → ℝ) (x y : ℝ) : ℝ :=
  p (u x y) / (x * y * (1 / 2 - x - y))

/-- Closed triangle, represented by its actual iterated integration bounds. -/
def triangle (x y : ℝ) : Prop :=
  x ∈ Icc alpha (alpha + d) ∧ y ∈ Icc (1 / 4) (top x)

noncomputable def loss (p : ℝ → ℝ) : ℝ :=
  4 * ∫ x in alpha..alpha + d, ∫ y in (1 / 4)..top x, kernel p x y

theorem alpha_pos : 0 < alpha := by norm_num [alpha]
theorem d_pos : 0 < d := by norm_num [d, alpha]
theorem q_pos : 0 < q := by norm_num [q]

theorem top_ge {x : ℝ} (hx : x ∈ Icc alpha (alpha + d)) : 1 / 4 ≤ top x := by
  dsimp [top, d] at *
  linarith [hx.2]

theorem triangle_coordinates {x y : ℝ} (h : triangle x y) :
    alpha ≤ x ∧ (1 / 4 : ℝ) ≤ y ∧ 2 * alpha ≤ 1 / 2 - x - y := by
  rcases h with ⟨hx, hy⟩
  dsimp [top] at hy
  exact ⟨hx.1, hy.1, by linarith [hy.2]⟩

theorem triangle_u_range {x y : ℝ} (h : triangle x y) :
    2 ≤ u x y ∧ u x y ≤ 927 / 400 := by
  obtain ⟨hx, hy, hz⟩ := triangle_coordinates h
  constructor
  · exact (le_div_iff₀ alpha_pos).2 (by linarith)
  · apply (div_le_iff₀ alpha_pos).2
    dsimp [alpha] at hx ⊢
    linarith

theorem kernel_bounds {p : ℝ → ℝ} {x y : ℝ} (h : triangle x y)
    (hp : 0 ≤ p (u x y) ∧ p (u x y) ≤ q) :
    0 ≤ kernel p x y ∧ kernel p x y ≤ 2 * q / alpha ^ 2 := by
  obtain ⟨hx, hy, hz⟩ := triangle_coordinates h
  have ha := alpha_pos
  have hx0 : 0 ≤ x := le_trans (le_of_lt ha) hx
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 < 1 / 2 - x - y := by linarith
  have hxy : alpha * (1 / 4) ≤ x * y :=
    mul_le_mul hx hy (by norm_num) hx0
  have hden : alpha ^ 2 / 2 ≤ x * y * (1 / 2 - x - y) := by
    have hh := mul_le_mul hxy hz (by positivity : 0 ≤ 2 * alpha)
      (mul_nonneg hx0 hy0)
    nlinarith
  have hden0 : 0 < x * y * (1 / 2 - x - y) :=
    mul_pos (mul_pos (lt_of_lt_of_le ha hx) (by linarith)) hz0
  constructor
  · exact div_nonneg hp.1 (le_of_lt hden0)
  · unfold kernel
    apply (div_le_iff₀ hden0).2
    have ha2 : 0 < alpha ^ 2 := sq_pos_of_pos ha
    have hh : q ≤ (2 * q / alpha ^ 2) * (alpha ^ 2 / 2) := by
      have he : (2 * q / alpha ^ 2) * (alpha ^ 2 / 2) = q := by
        field_simp
      rw [he]
    have hq : 0 ≤ q := le_of_lt q_pos
    exact hp.2.trans (hh.trans (mul_le_mul_of_nonneg_left hden (by positivity)))

/-- The affine section length is integrated, not supplied as an area hypothesis. -/
theorem affine_area :
    (∫ x in alpha..alpha + d, (top x - 1 / 4)) = d ^ 2 / 2 := by
  have he : (fun x : ℝ => top x - 1 / 4) = (fun x => (alpha + d) - x) := by
    funext x
    dsimp [top, d]
    ring
  rw [he, intervalIntegral.integral_sub
    (f := fun _ : ℝ => alpha + d) (g := fun x : ℝ => x)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

theorem constant_triangle_integral (C : ℝ) :
    (∫ x in alpha..alpha + d, ∫ _y in (1 / 4)..top x, C) = C * d ^ 2 / 2 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [intervalIntegral.integral_mul_const, affine_area]
  ring

/-- Standard analytic inputs only: bounded values on the triangle and integrable sections.
No table entries or integral certificate are assumed certified. -/
theorem loss_bounds (p : ℝ → ℝ)
    (hp : ∀ x y, triangle x y → 0 ≤ p (u x y) ∧ p (u x y) ≤ q)
    (hi : ∀ x ∈ Icc alpha (alpha + d),
      IntervalIntegrable (kernel p x) volume (1 / 4) (top x))
    (ho : IntervalIntegrable
      (fun x => ∫ y in (1 / 4)..top x, kernel p x y) volume alpha (alpha + d)) :
    0 ≤ loss p ∧ loss p ≤ 4 * q * (d / alpha) ^ 2 := by
  have hab : alpha ≤ alpha + d := by linarith [d_pos]
  have hn : ∀ x ∈ Icc alpha (alpha + d),
      0 ≤ ∫ y in (1 / 4)..top x, kernel p x y := by
    intro x hx
    apply intervalIntegral.integral_nonneg (top_ge hx)
    intro y hy
    exact (kernel_bounds ⟨hx, hy⟩ (hp x y ⟨hx, hy⟩)).1
  have hm : ∀ x ∈ Icc alpha (alpha + d),
      (∫ y in (1 / 4)..top x, kernel p x y) ≤
        ∫ _y in (1 / 4)..top x, 2 * q / alpha ^ 2 := by
    intro x hx
    apply intervalIntegral.integral_mono_on (top_ge hx) (hi x hx) intervalIntegrable_const
    intro y hy
    exact (kernel_bounds ⟨hx, hy⟩ (hp x y ⟨hx, hy⟩)).2
  have hc : IntervalIntegrable
      (fun x => ∫ _y in (1 / 4)..top x, 2 * q / alpha ^ 2)
      volume alpha (alpha + d) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    apply Continuous.intervalIntegrable
    unfold top
    fun_prop
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hab hn)
  · have hh := intervalIntegral.integral_mono_on hab ho hc hm
    rw [constant_triangle_integral] at hh
    unfold loss
    calc
      4 * (∫ x in alpha..alpha + d, ∫ y in (1 / 4)..top x, kernel p x y)
          ≤ 4 * ((2 * q / alpha ^ 2) * d ^ 2 / 2) := by linarith
      _ = 4 * q * (d / alpha) ^ 2 := by ring

end QuarterTrim
