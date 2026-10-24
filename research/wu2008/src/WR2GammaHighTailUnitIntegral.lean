import WR2GammaHighTailUnitSigma

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnit HighUnitSource Real
open scoped Classical

theorem boxed_sigma_pair_combined {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3,
      ∀ a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (windows j N),
        1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) →
      let W := windows j N
      (|boxedSigma20 N δ W a2 a3 b - boxedIntegral20 N δ W a2 a3 b| ≤
        (epsilon / 2) * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) ∧
      (|boxedSigma21 N δ W a3 b - boxedIntegral21 N δ W a3 b| ≤
        (epsilon / 2) * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) ∧
      (|boxedSigma20 N δ W a2 a3 b + boxedSigma21 N δ W a3 b -
        (boxedIntegral20 N δ W a2 a3 b + boxedIntegral21 N δ W a3 b)| ≤
        epsilon * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) := by
  obtain ⟨T, hT4, hT⟩ := boxed_sigma_pair_uniform hδ hδhi (half_pos he)
  refine ⟨T, hT4, ?_⟩
  intro N hN j a2 a3 b hw
  obtain ⟨h20, h21⟩ := hT N hN j a2 a3 b hw
  dsimp only at h20 h21 ⊢
  refine ⟨h20, h21, ?_⟩
  have ht := abs_add_le
    (boxedSigma20 N δ (windows j N) a2 a3 b -
      boxedIntegral20 N δ (windows j N) a2 a3 b)
    (boxedSigma21 N δ (windows j N) a3 b -
      boxedIntegral21 N δ (windows j N) a3 b)
  rw [show ∀ x y z w : ℝ, x - y + (z - w) = x + z - (y + w) by intros; ring] at ht
  linarith

theorem source_pair_integral {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3,
      ∀ a0 a1 a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (windows j N),
        1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) →
      let W := windows j N
      (unit20 N δ W a0 a1 a2 a3 b ≤ boxedIntegral20 N δ W a2 a3 b +
        (epsilon / 2) * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W) ∧
      (unit21 N δ W a0 a1 a2 a3 b ≤ boxedIntegral21 N δ W a3 b +
        (epsilon / 2) * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W) ∧
      (unit20 N δ W a0 a1 a2 a3 b + unit21 N δ W a0 a1 a2 a3 b ≤
        boxedIntegral20 N δ W a2 a3 b + boxedIntegral21 N δ W a3 b +
        epsilon * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W) := by
  obtain ⟨T, hT4, hT⟩ := boxed_sigma_pair_combined hδ hδhi he
  refine ⟨T, hT4, ?_⟩
  intro N hN j a0 a1 a2 a3 b hw
  obtain ⟨hs20, hs21⟩ := source_pair_le_boxed j (by omega) hδ hδhi a0 a1 a2 a3 b hw
  obtain ⟨h20, h21, hsum⟩ := hT N hN j a2 a3 b hw
  dsimp only at hs20 hs21 h20 h21 hsum ⊢
  have he20 := (le_abs_self _).trans h20
  have he21 := (le_abs_self _).trans h21
  have hesum := (le_abs_self _).trans hsum
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Literal original unit pair, retaining both same-phi J integrals. -/
theorem actual_unit_pair_integral {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      HighNonunit.actualUnit N δ (Wu04RemainingCore.row j) (windows j N) false +
        HighNonunit.actualUnit N δ (Wu04RemainingCore.row j) (windows j N) true ≤
      boxedIntegral20 N δ (windows j N) (fun _ => 1/(Wu04RemainingCore.row j).kappa2)
        (fun _ => 1/(Wu04RemainingCore.row j).kappa3) (fun _ => 1/(Wu04RemainingCore.row j).s) +
      boxedIntegral21 N δ (windows j N) (fun _ => 1/(Wu04RemainingCore.row j).kappa3)
        (fun _ => 1/(Wu04RemainingCore.row j).s) +
      ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  obtain ⟨T,hT,h⟩ := source_pair_integral hd hh he
  refine ⟨T,hT,fun N hN j => ?_⟩
  let p := Wu04RemainingCore.row j
  have hp := (row_analytic j).mother
  have hs := (row_analytic j).two_lt_s.le
  have hu := (h N hN j (fun _ => 1/p.S) (fun _ => 1/p.kappa1)
    (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s)
    (fun _ _ => parameter_outer_bounds hp hs)).2.2
  simpa only [HighNonunit.actualUnit, HighNonunit.word, unit20, unit21,
    Bool.false_eq_true, if_false, if_true, wuLocalCutoff, p] using hu

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.source_pair_integral
#print axioms WuPaper.R2GammaHigh.TailUnit.actual_unit_pair_integral
