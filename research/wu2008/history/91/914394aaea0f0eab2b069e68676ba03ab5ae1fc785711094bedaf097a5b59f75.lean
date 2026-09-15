import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGatePrimeMass
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureSource

/-! # Actual no-gate X masses bounded by the literal respective band integrals -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def fourthRowTripleNoGateIntegralMain {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
      fourthRowTripleNoGateIntegral eleven (omega3XPhi N d δ)

theorem fourthRowTripleNoGate_source_quadrature (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), ∀ eleven : Bool,
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        |fourthRowTripleNoGatePrimeSum R eleven (primeOrderedBuchstabWeight (omega3XPhi N d δ)) -
          fourthRowTripleNoGateIntegral eleven (omega3XPhi N d δ)| < ε := by
  let P := max 2 (1 / wuLocalExponent k δ)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (fourthRowTripleNoGate_buchstab_quadrature P ε (le_max_left _ _) hε)
  have hη := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd eleven
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    linarith [hg.2.2.1]
  exact hR0 _ ((hT N ((le_max_right _ _).trans hN)).trans hg.1) _ hφ
    (hg.2.2.2.trans (le_max_right _ _)) eleven

theorem fourthRowTripleNoGate_buchstab_integral (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowTripleNoGateBuchstab N δ W eleven ≤
        fourthRowTripleNoGateIntegralMain N δ W eleven +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hquad⟩ := fourthRowTripleNoGate_source_quadrature k hδ hδhi
    (mul_pos hε (wuLocalExponent_pos k hδ hδhi))
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb eleven W
  have hN2 : 2 ≤ N := by omega
  unfold fourthRowTripleNoGateBuchstab fourthRowTripleNoGateIntegralMain boxConvolutionReciprocalMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hg := omega3XPhi_source_bounds hN2 hδ hδhi hb hd
  have hlog := log_pos hg.2.1
  have hcoef : 0 ≤ (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by positivity
  have hdsc := le_of_lt ((le_abs_self _).trans_lt (hquad N hN i Δ V hb d hd eleven))
  have hsum := fourthRowTripleNoGate_prime_mass hN2 hδ hδhi hb hd eleven
  dsimp only at hsum hdsc
  have herr := omega3X_log_scale_error_le hN2 hδ hδhi hb hd hε.le
  have hmul := mul_le_mul_of_nonneg_left hdsc hcoef
  have hp :
      (∑ p ∈ fourthRowTripleNoGatePrimes N d δ eleven,
        omega3XScale N d p.1 p.2.1 p.2.2 *
          LiLiuPrereqBuchstab.buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        fourthRowTripleNoGateIntegral eleven (omega3XPhi N d δ) +
          ε * ((N : ℝ) / log N) / d := by
    nlinarith only [hsum, hmul, herr]
  convert mul_le_mul_of_nonneg_left hp
    (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _) using 1
  ring

theorem fourthRowTripleNoGate_X_main (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowTripleNoGateX N δ W eleven ≤
        fourthRowTripleNoGateIntegralMain N δ W eleven +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T1, hT1, hrough⟩ := fourthRowTripleNoGate_X_buchstab k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hquad⟩ := fourthRowTripleNoGate_buchstab_integral k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb eleven
  have h1 := hrough N ((le_max_left _ _).trans hN) i Δ V hb eleven
  have h2 := hquad N ((le_max_right _ _).trans hN) i Δ V hb eleven
  dsimp only at h1 h2 ⊢
  linarith

end Wu2008DoubleSieve
