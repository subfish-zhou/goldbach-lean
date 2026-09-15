import MathlibNt.Wu2008DoubleSieve.ReboxingParameter
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Uniform source-window replacement data

Wu04 (3.15), source lines 997--1065. The one threshold precedes every
legal box, both outer parameters, the terminal index, and every atom.
No coefficient continuity or convergence is used.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

/-- The actual dp cutoff is exactly the selected prime, not an
asymptotic or endpoint approximation. -/
theorem reboxing_atom_cutoff {D p : ℝ} (hD : 0 < D) (hp : 1 < p)
    (hs : 0 < log D / log p - 1) :
    (D / p) ^ (1 / (log D / log p - 1)) = p := by
  have hp0 : 0 < p := by linarith
  have hLp : 0 < log p := log_pos hp
  have hL : 0 < log D - log p := by
    have hh : 1 < log D / log p := by linarith
    have := (lt_div_iff₀ hLp).1 hh
    linarith
  have hbase : 0 < D / p := div_pos hD hp0
  have hbase1 : D / p ≠ 1 := by
    intro he
    have hh := log_div hD.ne' hp0.ne'
    rw [he, log_one] at hh
    linarith
  have he : 1 / (log D / log p - 1) = logb (D / p) p := by
    rw [logb, log_div hD.ne' hp0.ne']
    field_simp
  rw [he]
  exact rpow_logb hbase hbase1 hp0

theorem reboxingAlpha_previous {q Δ t j : ℝ} (hΔ : 0 < Δ) :
    reboxingAlpha q Δ t j / Δ = reboxingAlpha q Δ t (j - 1) := by
  have hh := reboxingAlpha_step (q := q) (t := t) (j := j - 1) hΔ
  have he : j - 1 + 1 = j := by ring
  rw [he] at hh
  rw [hh, mul_div_cancel_right₀ _ hΔ.ne']

/-- A genuine producer for the full geometric source data. The returned
terminal index also works at depth zero and when `s=t` (then it is zero).
Every supported atom has its own exact dp cutoff and lies in `[1,10]`. -/
theorem reboxing_source_parameters (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ r →
          q ^ (1 / t) ≤ reboxingAlpha q Δ t j ∧
          reboxingAlpha q Δ t j ≤ q ^ (1 / s) ∧
          reboxingAlpha q Δ t j / Δ = reboxingAlpha q Δ t ((j : ℝ) - 1) ∧
          1 ≤ reboxingS1 q Δ t j ∧ reboxingS1 q Δ t j ≤ 10 ∧
          1 ≤ reboxingS2 q Δ t i j ∧ reboxingS2 q Δ t i j ≤ 10 ∧
          ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          ∀ p ∈ primeWindow N (reboxingAlpha q Δ t ((j : ℝ) - 1))
              (reboxingAlpha q Δ t j),
            let u := log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1
            reboxingS1 q Δ t j ≤ u ∧ u ≤ reboxingS2 q Δ t i j ∧
              1 ≤ u ∧ u ≤ 10 ∧ wuLocalCutoff N δ (d * p) u = p := by
  obtain ⟨T, hT4, hT⟩ := reboxing_parameter_mesh_eventually k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  dsimp only
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  obtain ⟨hΔ, hq, hmesh⟩ := hT N hN i Δ V hb
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hΔ0 : 0 < Δ := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  obtain ⟨r, hrlo, hrhi⟩ := reboxingAlpha_exists_terminal hq.le hΔ hs0 hst
  refine ⟨r, hrlo, hrhi, ?_⟩
  intro j hj hjr
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have hαlo : q ^ (1 / t) ≤ reboxingAlpha q Δ t j := by
    simpa only [reboxingAlpha_zero] using hm hj0
  have hαhi : reboxingAlpha q Δ t j ≤ q ^ (1 / s) :=
    (hm (by exact_mod_cast hjr)).trans hrlo
  have hdom := reboxing_parameter_domain hq hΔ hs hst ht hj1 hαhi hmesh
  refine ⟨hαlo, hαhi, reboxingAlpha_previous hΔ0,
    hdom.1, hdom.2.1, hdom.2.2.1, hdom.2.2.2, ?_⟩
  intro d hd p hp
  have hN4 : 4 ≤ N := hT4.trans hN
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _).trans_le
      (hb.2.2.2.2.1 l)
  have hQ : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hD := reboxing_support_level_bounds hQ hΔ0 hV hd
  have hprev : 1 < reboxingAlpha q Δ t ((j : ℝ) - 1) := by
    have hh : 1 < reboxingAlpha q Δ t 0 := by
      rw [reboxingAlpha_zero]
      exact one_lt_rpow hq (by positivity)
    exact hh.trans_le (hm (by linarith))
  have hp' := mem_primeWindow.mp hp
  have hbnd := reboxing_parameter_bounds hq hΔ hD.1 hD.2 hprev hp'.2.2.1 hp'.2.2.2
  have hu1 := hdom.1.trans hbnd.1
  have hu10 := hbnd.2.trans hdom.2.2.2
  refine ⟨hbnd.1, hbnd.2, hu1, hu10, ?_⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
  have hD0 : 0 < (N : ℝ) ^ (1 / 2 - δ) / d := hq0.trans_le hD.1
  have hid := reboxing_atom_cutoff hD0 hp1 (by linarith : 0 <
    log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)
  simpa only [wuLocalCutoff, Nat.cast_mul, div_div] using hid

end Wu2008DoubleSieve
