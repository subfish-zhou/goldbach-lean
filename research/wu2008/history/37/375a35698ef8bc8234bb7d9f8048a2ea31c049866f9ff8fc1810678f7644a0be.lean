import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeTransport
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralBounds

/-!
# Paid modulus transport for the actual finite-threshold coefficients

The coefficient is the constructed A-H or a+h at depth k+1, not an
arbitrary continuous substitute. One base threshold precedes N0, N,
the entire source family, and both outer parameters.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem wu_effective_prime_transport_relative (upper : Bool) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let g := fun d p : ℕ => wuEffectiveCoefficient upper (k + 1) δ N0
          (log (((N : ℝ) ^ (1 / 2 - δ) / d) / p) / log p)
        |reboxingPrimeSum false N δ s t W g - reboxingPrimeSum true N δ s t W g| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_abs_le_eleven upper (k + 1) (by omega) hδ hδhi)
  have hpow : ∀ᶠ N : ℕ in atTop, max 4 (44 / (η * ε)) ≤ (N : ℝ) ^ η :=
    ((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp hpow
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht
  dsimp only
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have hN01 : T1 ≤ N0 := (le_max_left _ _).trans ((le_max_right _ _).trans hN0)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  have hlarge := hT2 N hN2
  let g := fun d p : ℕ => wuEffectiveCoefficient upper (k + 1) δ N0
    (log (((N : ℝ) ^ (1 / 2 - δ) / d) / p) / log p)
  have hg : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), |g d p| ≤ 11 := by
    intro d hd p hp
    exact hT1 N0 hN01 _
      (wu_buchstab_prime_parameter_mem (show 2 ≤ N by omega) hδ hδhi hb hs hst ht hd hp)
  have hf := reboxingPrimeSum_transport_bound hN4 hδ hδhi hb hs hst ht
    (by norm_num : (0 : ℝ) ≤ 11) ((le_max_left _ _).trans hlarge) hg
  have hY : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hcpos : 0 < 11 * (4 / (η * (N : ℝ) ^ η)) := by positivity
  have hTnon : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hf) hcpos
  have hc : 11 * (4 / (η * (N : ℝ) ^ η)) ≤ ε := by
    have hl := (div_le_iff₀ (mul_pos hη hε)).1 ((le_max_right _ _).trans hlarge)
    have h44 : 44 / (η * (N : ℝ) ^ η) ≤ ε :=
      (div_le_iff₀ (mul_pos hη hY)).2 (by nlinarith [hl])
    convert h44 using 1
    ring
  exact hf.trans (mul_le_mul_of_nonneg_right hc hTnon)

end Wu2008DoubleSieve
