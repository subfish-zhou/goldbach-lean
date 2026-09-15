import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryCount
import MathlibNt.Wu2008DoubleSieve.ReboxingGeometricBoundary
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The genuine R1 producer on all legal source boxes

Wu04 (3.15), (3.17), source lines 1020--1022 and 1113--1127.
The literal terminal-window sieve sum is paid relative to its own Theta.
The proof includes the empty convolution and a zero terminal index.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology

noncomputable def reboxingR1 {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (s t : ℝ) (r : ℕ) : ℝ :=
  reboxingBoundaryCount N (convolutionWuWindows N Δ V)
    (fun _ => reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r)
    (fun d => ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / s))

/-- The geometric worker's actual terminal endpoint theorem, weakened to
the constants used by the boundary PNT consumers. -/
theorem reboxingR1_endpoint_bounds {i k N r : ℕ} {δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) ∧
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) <
        reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t (r + 1))
    {d : ℕ} (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    let Y := reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r
    let Z := ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / s)
    (N : ℝ) ^ (δ ^ (k + 2)) ≤ Y ∧ Y ≤ Z ∧
      log (Z / Y) ≤ (2 * ((k : ℝ) + 1)) / log (N : ℝ) ^ (4 : ℕ) := by
  dsimp only
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 1 ≤ log (N : ℝ) := by
    apply (le_log_iff_exp_le (by linarith : (0 : ℝ) < N)).2
    have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [exp_one_lt_three]
  obtain ⟨hheight, hwindow⟩ := reboxing_terminal_boundary_geometry
    (show 2 ≤ N by omega) hδ hδhi hL hb hs hst ht hr.1 hr.2
  have hexp : δ ^ (k + 2) ≤ δ ^ (k + 1) / 10 := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hδhi (pow_nonneg hδ.le (k + 1))]
  refine ⟨(rpow_le_rpow_of_exponent_le hN1.le hexp).trans hheight, (hwindow d hd).1, ?_⟩
  exact (hwindow d hd).2.trans (div_le_div_of_nonneg_right
    (by nlinarith [show (0 : ℝ) ≤ k by positivity])
    (pow_nonneg (log_pos hN1).le 4))

/-- Actual R1 is `o(Theta)` uniformly over every legal source box.
The threshold depends only on fixed `k,δ,ε` and precedes the two outer
parameters, the terminal index and all convolution fibres. -/
theorem reboxingR1_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) ∧
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) <
          reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t (r + 1)) →
      0 ≤ reboxingR1 N δ Δ V s t r ∧
        reboxingR1 N δ Δ V s t r ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT⟩ := reboxing_boundary_relative (pow_pos hδ (k + 2))
    (show 0 < 2 * ((k : ℝ) + 1) by positivity) hε
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (4 : ℕ)] with N hN hN4
  intro he i Δ V hb s t hs hst ht r hr
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hQ1 : 1 < (N : ℝ) ^ (1 / 2 - δ) := one_lt_rpow hN1 (by linarith)
  have hw1 : 1 < (N : ℝ) ^ (δ ^ (k + 1)) := one_lt_rpow hN1 (pow_pos hδ _)
  have hQN : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1.le
      (show 1 / 2 - δ ≤ 1 by linarith)
  have hsupport := fun d hd => boxSquaredPrefixes_support hw1 hQ1 hQN
    hb.2.2.2.2.1 hb.2.2.2.2.2 (Δ := Δ) (d := d) hd
  refine ⟨reboxingBoundaryCount_nonneg _ _ _ _, ?_⟩
  apply hT N hN he i ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
    (fun _ => reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r)
    (fun d => ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / s))
    (fun d hd => (hsupport d hd).1) (fun d hd => (hsupport d hd).2)
  intro d hd
  exact reboxingR1_endpoint_bounds (by omega) hδ hδhi hb hs hst ht hr hd

end Wu2008DoubleSieve
