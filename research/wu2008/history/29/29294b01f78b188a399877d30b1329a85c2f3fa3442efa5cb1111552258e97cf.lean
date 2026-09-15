import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabNormalization
import MathlibNt.Wu2008DoubleSieve.Omega3XFiniteRough

/-!
# Consuming fixed-cap Buchstab asymptotics on every actual X fibre

The cap and the lower gap are fixed from k and delta before the analytic
threshold. Qualitative relative convergence is used without a logarithmic rate.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem omega3X_buchstab_uniform (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ p ∈ omega3XPrimes N δ s t d,
        let x := omega3XScale N d p.1 p.2.1 p.2.2
        let y := (p.2.1 : ℝ)
        let B := x * buchstab (log x / log y) / log y
        primeErrorStart ≤ y ∧ 0 < B ∧
          |(roughCount x y : ℝ) - B| ≤ ε * (x / log y) := by
  obtain ⟨u0, M, _, hu0, hη, _, hu0M, hg⟩ :=
    omega3X_fixed_compact_geometry k hδ hδhi
  have hM : 2 ≤ M := by
    have : (1 : ℝ) < M := hu0.trans hu0M
    have : 1 < M := by exact_mod_cast this
    omega
  obtain ⟨X, _, hX⟩ := roughCount_uniform_buchstab_fixed M hM hu0 hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max X primeErrorStart)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd s t hs hst ht p hp
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨_, hy, hyx, hyg, hxg, _, _, _, hu⟩ :=
    hg N (by omega) i Δ V hb d hd s t hs hst ht p hp
  dsimp only at hy hyx hyg hxg hu ⊢
  have hgrowth := hT N ((le_max_right _ _).trans hN)
  have hxX := ((le_max_left X primeErrorStart).trans hgrowth).trans hxg
  have hyStart := ((le_max_right X primeErrorStart).trans hgrowth).trans hyg
  have hy1 : (1 : ℝ) < p.2.1 := by linarith
  obtain ⟨_, _, _, hcoord, hnorm⟩ := omega3X_buchstab_coordinates hy1 hyx
  obtain ⟨hpos, hrel⟩ := hX _ hxX _ hu
  rw [← hcoord, hnorm] at hrel
  rw [hnorm] at hpos
  refine ⟨hyStart, hpos, ?_⟩
  let B := omega3XScale N d p.1 p.2.1 p.2.2 *
    buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1
  have heq : (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) / B - 1 =
      ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) - B) / B := by
    have hB : B ≠ 0 := hpos.ne'
    field_simp
  change |(roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) / B - 1| < ε at hrel
  rw [heq, abs_div, abs_of_pos hpos] at hrel
  exact ((div_lt_iff₀ hpos).mp hrel).le.trans
    (mul_le_mul_of_nonneg_left (omega3X_buchstab_main_term_bounds hy1 hyx).2 hε.le)

theorem omega3XRoughMajorant_le_buchstab_error (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3XRoughMajorant N δ s t W ≤ omega3XBuchstabMain N δ s t W +
          ε * (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
            ∑ p ∈ omega3XPrimes N δ s t d,
              omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) := by
  obtain ⟨T, hT4, hT⟩ := omega3X_buchstab_uniform k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  dsimp only
  unfold omega3XRoughMajorant omega3XBuchstabMain
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro p hp
  have h := (hT N hN i Δ V hb d hd s t hs hst ht p hp).2.2
  have he := (le_abs_self ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) -
    omega3XScale N d p.1 p.2.1 p.2.2 *
      buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1)).trans h
  have hm := mul_le_mul_of_nonneg_left he
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
  nlinarith only [hm]

end Wu2008DoubleSieve
