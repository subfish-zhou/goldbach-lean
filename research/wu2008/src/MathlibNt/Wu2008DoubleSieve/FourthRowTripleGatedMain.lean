import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedPrimeMass
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureSource

/-! # The unconditional actual gated main masses, uniformly over original boxes -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def fourthRowTripleGatedIntegralMain {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
      fourthRowTripleGatedIntegral ten (omega3XPhi N d δ)

theorem fourthRowTripleGated_source_quadrature (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), ∀ ten : Bool,
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        |fourthRowTripleGatedPrimeSum R ten (primeOrderedBuchstabWeight (omega3XPhi N d δ)) -
          fourthRowTripleGatedIntegral ten (omega3XPhi N d δ)| < ε := by
  let P := max 2 (1 / wuLocalExponent k δ)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (fourthRowTripleGated_buchstab_quadrature P ε (le_max_left _ _) hε)
  have hη := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd ten
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    linarith [hg.2.2.1]
  exact hR0 _ ((hT N ((le_max_right _ _).trans hN)).trans hg.1) _ hφ
    (hg.2.2.2.trans (le_max_right _ _)) ten

theorem fourthRowTripleGated_buchstab_integral (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ ten : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowTripleGatedBuchstab N δ W ten ≤ fourthRowTripleGatedIntegralMain N δ W ten +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hquad⟩ := fourthRowTripleGated_source_quadrature k hδ hδhi
    (mul_pos hε (wuLocalExponent_pos k hδ hδhi))
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb ten W
  have hN2 : 2 ≤ N := by omega
  unfold fourthRowTripleGatedBuchstab fourthRowTripleGatedIntegralMain boxConvolutionReciprocalMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hg := omega3XPhi_source_bounds hN2 hδ hδhi hb hd
  have hlog := log_pos hg.2.1
  have hcoef : 0 ≤ (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by positivity
  have hdsc := le_of_lt ((le_abs_self _).trans_lt (hquad N hN i Δ V hb d hd ten))
  have hsum := fourthRowTripleGated_prime_mass hN2 hδ hδhi hb hd ten
  dsimp only at hsum hdsc
  have herr := omega3X_log_scale_error_le hN2 hδ hδhi hb hd hε.le
  have hmul := mul_le_mul_of_nonneg_left hdsc hcoef
  have hp :
      (∑ p ∈ fourthRowTripleGatedPrimes N d δ ten,
        omega3XScale N d p.1 p.2.1 p.2.2 *
          LiLiuPrereqBuchstab.buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        fourthRowTripleGatedIntegral ten (omega3XPhi N d δ) + ε * ((N : ℝ) / log N) / d := by
    nlinarith only [hsum, hmul, herr]
  convert mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _) using 1
  ring

theorem fourthRowTripleGated_X_main (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ ten : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowTripleGatedX N δ W (fourthRowTripleGatedProfiles N δ W ten) ≤
        fourthRowTripleGatedIntegralMain N δ W ten +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T1, hT1, hrough⟩ := fourthRowTripleGated_X_buchstab k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hquad⟩ := fourthRowTripleGated_buchstab_integral k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb ten
  have h1 := hrough N ((le_max_left _ _).trans hN) i Δ V hb ten
  have h2 := hquad N ((le_max_right _ _).trans hN) i Δ V hb ten
  dsimp only at h1 h2 ⊢
  linarith

end Wu2008DoubleSieve
