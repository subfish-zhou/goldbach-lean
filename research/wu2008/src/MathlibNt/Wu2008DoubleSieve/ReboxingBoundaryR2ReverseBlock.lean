import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2Reverse
import MathlibNt.Wu2008DoubleSieve.ReboxingBlockSum

/-!
# Consuming reverse R2 in the actual sorted-block lower comparison

The sign is `raw = cutoff(s2) - reverse error`. Actual attained lower
improvements are used without a nonnegativity assumption on `a+h`.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem reboxingGeometricRaw_eq_s2_sub_R2Reverse {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) :
    reboxingGeometricRaw N δ Δ V t r =
      reboxingGeometricCutoff N δ Δ V t r
        (fun j => reboxingS2 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t i (j + 1)) -
      reboxingR2Reverse N δ Δ V t r := by
  unfold reboxingGeometricRaw reboxingGeometricCutoff reboxingR2Reverse
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

/-- The complete reverse cutoff payment is physically consumed with
the actual inserted source-box lower comparison. Both thresholds precede
`N0`, and the one epsilon payment follows the full finite block sum. -/
theorem reboxingGeometricRaw_lower_s2 (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingGeometricMain false k N0 N δ Δ V t r
            (fun j => reboxingS2 q Δ t i (j + 1)) -
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        reboxingGeometricRaw N δ Δ V t r := by
  obtain ⟨T1, hT14, hblocks⟩ := wu_reboxed_block_upper_lower k hδ hδhi
  obtain ⟨T2, _, hparameters⟩ := reboxing_source_parameters k hδ hδhi
  obtain ⟨T3, hR2⟩ := reboxingR2Reverse_relative k hδ hδhi hε
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have h1 : T1 ≤ N0 := (le_max_left _ _).trans hN0
  have h2 : T2 ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  have h3 : T3 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  obtain ⟨r, hrlo, hrhi, hp⟩ := hparameters N h2 i Δ V hb s t hs hst ht
  refine ⟨r, hrlo, hrhi, ?_⟩
  have hcut :
      reboxingGeometricMain false k N0 N δ Δ V t r
          (fun j => reboxingS2 q Δ t i (j + 1)) ≤
        reboxingGeometricCutoff N δ Δ V t r
          (fun j => reboxingS2 q Δ t i (j + 1)) := by
    unfold reboxingGeometricCutoff reboxingGeometricMain
    apply Finset.sum_le_sum
    intro j hj
    have hpj := hp (j + 1) (by omega) (by have := mem_range.mp hj; omega)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hpj
    have hcmp := hblocks N0 h1 N hN he i Δ V hb s t
      (reboxingAlpha q Δ t (j + 1)) hs (by linarith) ht hpj.1 hpj.2.1
      (reboxingS2 q Δ t i (j + 1)) hpj.2.2.2.2.2.1 hpj.2.2.2.2.2.2.1
    have hprev := hpj.2.2.1
    simpa only [q, hprev, wuEffectiveCoefficient, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_add, Nat.cast_one] using hcmp.1
  have herror := (hR2 N h3 he i Δ V hb s t hs hst ht r hrlo).2
  rw [reboxingGeometricRaw_eq_s2_sub_R2Reverse]
  exact sub_le_sub hcut herror

end Wu2008DoubleSieve
