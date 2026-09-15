import MathlibNt.Wu2008DoubleSieve.Gamma5GainGeometry

/-!
# Actual Delta micro-windows in a fixed exponent rectangle
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

noncomputable def gamma5GainStep (R Δ : ℝ) : ℝ := log Δ / log R
noncomputable def gamma5GainSize (R Δ A B : ℝ) : ℕ := ⌊(B - A) / gamma5GainStep R Δ⌋₊
noncomputable def gamma5GainPoint (R Δ A : ℝ) (j : ℕ) : ℝ := A + j * gamma5GainStep R Δ
noncomputable def gamma5GainTerminal (R Δ A B : ℝ) : ℝ :=
  gamma5GainPoint R Δ A (gamma5GainSize R Δ A B)
noncomputable def gamma5GainEnd (R Δ A : ℝ) (j : ℕ) : ℝ := R ^ gamma5GainPoint R Δ A (j + 1)

noncomputable def gamma5GainPacking {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (r : Gamma5GainRectangle) : Finset Gamma5ClassicalLabel :=
  boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
    (primeWindow N ((gamma5GainScale N δ V) ^ r.A)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.A r.B) ×ˢ
    primeWindow N ((gamma5GainScale N δ V) ^ r.C)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.C r.D))

theorem gamma5Gain_step_pos {R Δ : ℝ} (hR : 1 < R) (hΔ : 1 < Δ) :
    0 < gamma5GainStep R Δ := div_pos (log_pos hΔ) (log_pos hR)

theorem gamma5Gain_terminal_bounds {R Δ A B : ℝ} (hR : 1 < R) (hΔ : 1 < Δ) (hAB : A ≤ B) :
    A ≤ gamma5GainTerminal R Δ A B ∧ gamma5GainTerminal R Δ A B ≤ B ∧
      B < gamma5GainTerminal R Δ A B + gamma5GainStep R Δ := by
  have hh := gamma5Gain_step_pos hR hΔ
  have hl := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hAB) hh.le))
  have hu := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((B - A) / gamma5GainStep R Δ))
  unfold gamma5GainTerminal gamma5GainPoint gamma5GainSize
  refine ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le), ?_, ?_⟩ <;> linarith

theorem gamma5Gain_point_strictMono {R Δ : ℝ} (hR : 1 < R) (hΔ : 1 < Δ) (A : ℝ) :
    StrictMono (gamma5GainPoint R Δ A) := by
  intro j l hjl
  exact add_lt_add_right
    (mul_lt_mul_of_pos_right (by exact_mod_cast hjl) (gamma5Gain_step_pos hR hΔ)) _

theorem gamma5Gain_point_bounds {R Δ A B : ℝ} {j : ℕ}
    (hR : 1 < R) (hΔ : 1 < Δ) (hAB : A ≤ B) (hj : j < gamma5GainSize R Δ A B) :
    A ≤ gamma5GainPoint R Δ A j ∧ gamma5GainPoint R Δ A (j + 1) ≤ B := by
  have hm := (gamma5Gain_point_strictMono hR hΔ A).monotone
  exact ⟨by simpa [gamma5GainPoint] using hm (Nat.zero_le j),
    (hm (by omega)).trans (gamma5Gain_terminal_bounds hR hΔ hAB).2.1⟩

theorem gamma5Gain_point_power {R Δ : ℝ} (hR : 1 < R) (hΔ : 1 < Δ) (A : ℝ) (j : ℕ) :
    R ^ gamma5GainPoint R Δ A j = reboxingAlpha (R ^ A) Δ 1 j := by
  have hR0 : 0 < R := by linarith
  have hh : R ^ gamma5GainStep R Δ = Δ := by
    rw [gamma5GainStep, rpow_def_of_pos hR0, mul_div_cancel₀ _ (log_pos hR).ne',
      exp_log (by linarith : 0 < Δ)]
  rw [gamma5GainPoint, rpow_add hR0, mul_comm (j : ℝ), rpow_mul hR0.le, hh]
  simp [reboxingAlpha]

theorem gamma5Gain_end_lower {R Δ : ℝ} (hR : 1 < R) (hΔ : 1 < Δ) (A : ℝ) (j : ℕ) :
    gamma5GainEnd R Δ A j / Δ = R ^ gamma5GainPoint R Δ A j := by
  unfold gamma5GainEnd
  rw [gamma5Gain_point_power hR hΔ, gamma5Gain_point_power hR hΔ]
  push_cast
  rw [reboxingAlpha_step (by linarith : 0 < Δ), mul_div_cancel_right₀ _ (by linarith : Δ ≠ 0)]

theorem gamma5Gain_grid_sum {R Δ : ℝ} (hR : 1 < R) (hΔ : 1 < Δ)
    (N : ℕ) (A B : ℝ) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N (R ^ A) (R ^ gamma5GainTerminal R Δ A B), f p) =
      ∑ j ∈ range (gamma5GainSize R Δ A B),
        ∑ p ∈ primeWindow N (gamma5GainEnd R Δ A j / Δ) (gamma5GainEnd R Δ A j), f p := by
  simp_rw [gamma5Gain_end_lower hR hΔ, gamma5GainEnd, gamma5Gain_point_power hR hΔ]
  have h := reboxingAlpha_sum_partition (rpow_pos_of_pos (by linarith : 0 < R) A)
    hΔ N (gamma5GainSize R Δ A B) f (t := 1)
  simpa [gamma5GainTerminal, reboxingAlpha_zero, gamma5Gain_point_power hR hΔ] using h

theorem gamma5Gain_packing_sum {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) (r : Gamma5GainRectangle)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ gamma5GainPacking N δ Δ V r, f x) =
      ∑ j ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
        ∑ l ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
          ∑ x ∈ gamma5GainCell N Δ
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j)
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l)
            (convolutionWuWindows N Δ V), f x := by
  unfold gamma5GainPacking gamma5GainCell
  simp_rw [sum_product]
  simp_rw [gamma5Gain_grid_sum hR hΔ]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro d _
  rw [sum_comm]

theorem gamma5Gain_grid_disjoint {R Δ : ℝ} (hR : 1 < R) (hΔ : 1 < Δ)
    (N : ℕ) (A : ℝ) :
    Pairwise (fun j l : ℕ => Disjoint
      (primeWindow N (gamma5GainEnd R Δ A j / Δ) (gamma5GainEnd R Δ A j))
      (primeWindow N (gamma5GainEnd R Δ A l / Δ) (gamma5GainEnd R Δ A l))) := by
  intro j l hjl
  simp_rw [gamma5Gain_end_lower hR hΔ, gamma5GainEnd]
  have hm := (gamma5Gain_point_strictMono hR hΔ A).monotone
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  rcases lt_or_gt_of_ne hjl with h | h
  · have hh := rpow_le_rpow_of_exponent_le hR.le (hm (show j + 1 ≤ l by omega))
    exact (not_lt_of_ge hq'.2.2.1) (hp'.2.2.2.trans_le hh)
  · have hh := rpow_le_rpow_of_exponent_le hR.le (hm (show l + 1 ≤ j by omega))
    exact (not_lt_of_ge hp'.2.2.1) (hq'.2.2.2.trans_le hh)

end Wu2008DoubleSieve
