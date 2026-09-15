import MathlibNt.Wu2008DoubleSieve.ReboxingBlockComparison
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralBounds

/-!
# Consuming the actual block comparisons and the paid R2

All blocks are summed before the single relative error is paid. This
connects the actual prime cutoff to the sorted inserted-box comparisons;
the block main terms still retain their exact inserted Theta.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def reboxingGeometricRaw {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ p ∈ primeWindow N
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j)
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)),
      (sourceSieveCount N (d * p) ((d * p) * N) (p : ℝ) : ℝ)

noncomputable def reboxingGeometricCutoff {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ p ∈ primeWindow N
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j)
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)),
      (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) (u j)) : ℝ)

noncomputable def reboxingGeometricMain {i : ℕ} (upper : Bool) (k N0 N : ℕ)
    (δ Δ : ℝ) (V : Fin i → ℝ) (t : ℝ) (r : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range r, wuEffectiveCoefficient upper (k + 1) δ N0 (u j) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
      (Fin.cons
        (primeWindow N
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j)
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)))
        (convolutionWuWindows N Δ V))

theorem reboxingGeometricRaw_eq_s1_add_R2 {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) :
    reboxingGeometricRaw N δ Δ V t r =
      reboxingGeometricCutoff N δ Δ V t r
        (fun j => reboxingS1 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) +
      reboxingR2 N δ Δ V t r := by
  unfold reboxingGeometricRaw reboxingGeometricCutoff reboxingR2
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

/-- The actual upper R2 is consumed once after summing every sorted
source block. There is no assumed raw-sum estimate or moving block factor. -/
theorem reboxingGeometricRaw_upper_s1 (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingGeometricRaw N δ Δ V t r ≤
          reboxingGeometricMain true k N0 N δ Δ V t r
            (fun j => reboxingS1 q Δ t (j + 1)) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hblocks⟩ := wu_reboxed_block_upper_lower k hδ hδhi
  obtain ⟨T2, _, hparameters⟩ := reboxing_source_parameters k hδ hδhi
  obtain ⟨T3, hR2⟩ := reboxingR2_relative k hδ hδhi hε
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
      reboxingGeometricCutoff N δ Δ V t r (fun j => reboxingS1 q Δ t (j + 1)) ≤
        reboxingGeometricMain true k N0 N δ Δ V t r
          (fun j => reboxingS1 q Δ t (j + 1)) := by
    unfold reboxingGeometricCutoff reboxingGeometricMain
    apply Finset.sum_le_sum
    intro j hj
    have hpj := hp (j + 1) (by omega) (by have := mem_range.mp hj; omega)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hpj
    have hcmp := hblocks N0 h1 N hN he i Δ V hb s t
      (reboxingAlpha q Δ t (j + 1)) hs (by linarith) ht hpj.1 hpj.2.1
      (reboxingS1 q Δ t (j + 1)) hpj.2.2.2.1 hpj.2.2.2.2.1
    have hprev := hpj.2.2.1
    simpa only [q, hprev, wuEffectiveCoefficient, if_true,
      Nat.cast_add, Nat.cast_one] using hcmp.2
  have herror := (hR2 N h3 he i Δ V hb s t hs hst ht r hrlo).2
  rw [reboxingGeometricRaw_eq_s1_add_R2]
  exact add_le_add hcut herror

end Wu2008DoubleSieve
