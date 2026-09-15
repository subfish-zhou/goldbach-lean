import Wu18938Campaign.M5.StrictCorner

noncomputable section

namespace Wu18938Campaign.M5.KernelCorner

open Real Set MeasureTheory
open Wu18938Campaign.M5.StrictCorner

def parameter (δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  (1 / 2 - δ - z.1 - z.2) / (100 / 1327)

def kernel (δ : ℝ) (p : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  p (parameter δ z) / (z.1 * z.2 * (1 / 2 - δ - z.1 - z.2))

def denominatorFloor : ℝ :=
  (100 / 1327) * (25 / 206) * (3 * (100 / 1327) - (25 / 206) - 1 / 100)

theorem denominatorFloor_pos : 0 < denominatorFloor := by
  norm_num [denominatorFloor]

theorem envelope_parameter {δ : ℝ} {z : ℝ × ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 100) (hz : z ∈ originalEnvelope) :
    parameter δ z ∈ Icc (1 : ℝ) 5 := by
  obtain ⟨⟨hx, hx'⟩, hy, hy'⟩ := hz
  dsimp [parameter]
  constructor <;> linarith

theorem envelope_denominator {δ : ℝ} {z : ℝ × ℝ}
    (hδhi : δ ≤ 1 / 100) (hz : z ∈ originalEnvelope) :
    denominatorFloor ≤ z.1 * z.2 * (1 / 2 - δ - z.1 - z.2) := by
  have hx : 0 ≤ z.1 := (by norm_num : (0 : ℝ) ≤ 100 / 1327).trans hz.1.1
  have hy : 0 ≤ z.2 := (by norm_num : (0 : ℝ) ≤ 25 / 206).trans hz.2.1
  have hz' : 3 * (100 / 1327 : ℝ) - (25 / 206) - 1 / 100 ≤
      1 / 2 - δ - z.1 - z.2 := by linarith [hz.1.2, hz.2.2]
  exact mul_le_mul
    (mul_le_mul hz.1.1 hz.2.1 (by norm_num) hx) hz' (by norm_num)
    (mul_nonneg hx hy)

theorem kernel_measurable {p : ℝ → ℝ} (hp : Measurable p) (δ : ℝ) :
    Measurable (kernel δ p) := by
  unfold kernel parameter
  exact (hp.comp (by fun_prop)).div (by fun_prop)

theorem kernel_bound {δ : ℝ} {p : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 100)
    (hp : ∀ s ∈ Icc (1 : ℝ) 5, |p s| ≤ 10)
    {z : ℝ × ℝ} (hz : z ∈ originalEnvelope) :
    ‖kernel δ p z‖ ≤ 10 / denominatorFloor := by
  have hd := envelope_denominator hδhi hz
  rw [Real.norm_eq_abs, kernel, abs_div,
    abs_of_pos (denominatorFloor_pos.trans_le hd)]
  exact div_le_div₀ (by norm_num) (hp _ (envelope_parameter hδ hδhi hz))
    denominatorFloor_pos hd

theorem original_kernel_uniform_error {δ η : ℝ} {p : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 100) (hη : 0 ≤ η) (hηhi : η ≤ 1 / 100)
    (hm : Measurable p) (hp : ∀ s ∈ Icc (1 : ℝ) 5, |p s| ≤ 10) :
    |originalMass (kernel δ p) 0 - originalMass (kernel δ p) η| ≤
      4 * (10 / denominatorFloor) *
        ((25 / 206 : ℝ) - (100 / 1327) / 2) * η :=
  original_uniform_error hη hηhi (kernel_measurable hm δ)
    (fun _ hz => kernel_bound hδ hδhi hp hz)

theorem original_kernel_uniform_limit {ε : ℝ} (hε : 0 < ε) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 / 100 ∧
      ∀ η : ℝ, 0 < η → η < η0 →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 100 →
      ∀ p : ℝ → ℝ, Measurable p →
        (∀ s ∈ Icc (1 : ℝ) 5, |p s| ≤ 10) →
        |originalMass (kernel δ p) 0 - originalMass (kernel δ p) η| < ε := by
  obtain ⟨η0, hη0, hη0hi, h⟩ := original_uniform_limit
    (K := 10 / denominatorFloor) (by have := denominatorFloor_pos; positivity) hε
  refine ⟨η0, hη0, hη0hi, ?_⟩
  intro η hη hηhi δ hδ hδhi p hm hp
  exact h η hη hηhi (kernel δ p) (kernel_measurable hm δ)
    (fun _ hz => kernel_bound hδ hδhi hp hz)

end Wu18938Campaign.M5.KernelCorner
