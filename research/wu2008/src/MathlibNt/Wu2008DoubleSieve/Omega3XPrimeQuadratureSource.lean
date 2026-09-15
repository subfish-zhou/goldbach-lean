import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureFinite
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralEnvelope
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabSource

/-!
# Actual X prime quadrature with one source-family threshold

Wu04, TeX2240--2252. The additive error is paid on the identical
coefficient reciprocal mass; no division by the integral or width occurs.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def omega3XIntegralMain {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) /
      ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        omega3XIntegral s t (omega3XPhi N d δ)

theorem omega3X_ordered_quadrature_uniform (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        |primeOrderedTripleSum R (1 / t) (1 / s)
            (primeOrderedBuchstabWeight (omega3XPhi N d δ)) -
          omega3XIntegral s t (omega3XPhi N d δ)| < ε := by
  let P := max 2 (1 / wuLocalExponent k δ)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (primeOrdered_buchstab_uniform P ε (le_max_left _ _) hε)
  have hη := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd s t hs hst ht
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have := hg.2.2.1
    have : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    linarith
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  exact hR0 _ hlarge _ _ _ hφ (hg.2.2.2.trans (le_max_right _ _))
    (one_div_le_one_div_of_le (by linarith) ht)
    (one_div_le_one_div_of_le (by linarith) hst)
    (one_div_le_one_div_of_le (by norm_num) hs)

theorem omega3X_log_scale_error_le {i k N d : ℕ} {δ Δ ε : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hε : 0 ≤ ε) :
    (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        (ε * wuLocalExponent k δ) ≤ ε * ((N : ℝ) / log N) / d := by
  have hη := wuLocalExponent_pos k hδ hδhi
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hl := log_le_log (rpow_pos_of_pos hN0 _) hg.1
  rw [log_rpow hN0] at hl
  calc
    _ = (ε * wuLocalExponent k δ * ((N : ℝ) / d)) /
        log ((N : ℝ) ^ (1 / 2 - δ) / d) := by ring
    _ ≤ (ε * wuLocalExponent k δ * ((N : ℝ) / d)) /
        (wuLocalExponent k δ * log N) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hl
    _ = _ := by field_simp

/-- The requested actual finite Buchstab main-sum quadrature. -/
theorem omega3XBuchstabMain_le_integral_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3XBuchstabMain N δ s t W ≤ omega3XIntegralMain N δ s t W +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  have hη := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT4, hT⟩ := omega3X_ordered_quadrature_uniform k hδ hδhi (mul_pos hε hη)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN2 : 2 ≤ N := by omega
  dsimp only
  unfold omega3XBuchstabMain omega3XIntegralMain boxConvolutionReciprocalMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hg := omega3XPhi_source_bounds hN2 hδ hδhi hb hd
  have hlog := log_pos hg.2.1
  have hcoef : 0 ≤ (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) :=
    by positivity
  have hdisc := le_of_lt ((le_abs_self _).trans_lt (hT N hN i Δ V hb d hd s t hs hst ht))
  have hsum := omega3XPrime_buchstab_le_ordered hN2 hδ hδhi hb hd hs hst ht
  dsimp only at hsum hdisc
  have herr := omega3X_log_scale_error_le hN2 hδ hδhi hb hd hε.le
  have hmul := mul_le_mul_of_nonneg_left hdisc hcoef
  have hpoint :
      (∑ p ∈ omega3XPrimes N δ s t d,
        let x := omega3XScale N d p.1 p.2.1 p.2.2
        x * LiLiuPrereqBuchstab.buchstab (log x / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        omega3XIntegral s t (omega3XPhi N d δ) + ε * ((N : ℝ) / log N) / d := by
    nlinarith only [hsum, hmul, herr]
  have hw := mul_le_mul_of_nonneg_left hpoint
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
  convert hw using 1
  ring

/-- The raw X now has no residual finite prime sum on its right-hand side. -/
theorem omega3SieveX_le_integral_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3SieveX N δ s t W ≤ omega3XIntegralMain N δ s t W +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T1, hT14, hT1⟩ := omega3SieveX_le_buchstab_paid k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3XBuchstabMain_le_integral_paid k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have h1 := hT1 N ((le_max_left _ _).trans hN) i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i Δ V hb s t hs hst ht
  dsimp only at h1 h2 ⊢
  linarith

end Wu2008DoubleSieve
