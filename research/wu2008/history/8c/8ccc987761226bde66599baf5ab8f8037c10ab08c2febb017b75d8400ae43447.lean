import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabUniform
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeMassSource
import MathlibNt.Wu2008DoubleSieve.Omega3XSource

/-!
# The actual X is bounded by its finite Buchstab main sum

Wu04, TeX2215--2238. Prime reciprocal mass pays the qualitative Buchstab
error. The independent repeated-p1 power-saving error is paid separately.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3XRoughMajorant_le_buchstab_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3XRoughMajorant N δ s t W ≤ omega3XBuchstabMain N δ s t W +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨C, T1, hC, hT14, hT1⟩ := omega3X_weighted_scale_mass_uniform k hδ hδhi
  obtain ⟨T2, _, hT2⟩ :=
    omega3XRoughMajorant_le_buchstab_error k hδ hδhi (div_pos hε hC)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  have he := mul_le_mul_of_nonneg_left h1 (div_pos hε hC).le
  have hcancel :
      ε / C * (C * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) =
      ε * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    field_simp
  rw [hcancel] at he
  exact h2.trans (add_le_add le_rfl he)

/-- The physical raw X, with no rough-count or analytic premise remaining. -/
theorem omega3SieveX_le_buchstab_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3SieveX N δ s t W ≤ omega3XBuchstabMain N δ s t W +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T1, hT14, hT1⟩ := omega3SieveX_le_rough_paid k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3XRoughMajorant_le_buchstab_paid k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  linarith

end Wu2008DoubleSieve
