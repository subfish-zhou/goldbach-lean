import MathlibNt.Wu2008DoubleSieve.Gamma16MainMass
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralNormalization

/-! # Sharp Li and singular-series normalization on the original boxTheta -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def gamma16IntegralMain {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
      gamma16FourthIntegral (omega3XPhi N d δ)

theorem gamma16_integral_scaled {i k N : ℕ} {δ Δ K τ : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hK : 0 ≤ K)
    (hli : (N : ℝ) / log N ≤ (1 + τ) * logarithmicIntegral N) :
    let W := convolutionWuWindows N Δ V
    gamma16IntegralMain N δ W * (K * wuSingularSeries N / log N) ≤
      ((1 + τ) * K / 4 * gamma16FourthIntegralEnvelope) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let E := gamma16FourthIntegralEnvelope
  let A := ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) / (d * log (Q / d))
  let U := ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log (Q / d))
  have hN0 : 0 < N := by omega
  have hC0 := wuSingularSeries_pos N hN0
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hE : 0 ≤ E := gamma16_fourth_envelope_bounds.1
  have hA : 0 ≤ A := sum_nonneg fun d hd => by
    have hl := log_pos (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
    dsimp [Q]
    positivity
  have hS : wuSingularSeries N * A ≤ U := by
    dsimp [A, U]
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 := boxConvolutionSupport_pos
      (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have htpos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have htot : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl := log_pos (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
    have hC := wuSingularSeries_le_mul hN0 hd0
    have hCd := hC0.trans_le hC
    calc
      _ = (convolutionCoeff W d : ℝ) * wuSingularSeries N /
          ((d : ℝ) * log (Q / d)) := by ring
      _ ≤ _ := by dsimp [Q]; gcongr
  have hU : 0 ≤ U := (mul_nonneg hC0.le hA).trans hS
  have he : gamma16IntegralMain N δ W ≤ (N : ℝ) * E * A := by
    unfold gamma16IntegralMain
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    dsimp only [A]
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
    have hl := log_pos hg.2.1
    have hφ : 2 ≤ omega3XPhi N d δ := by
      have hh : 0 < 2 * δ / (1 / 2 - δ) := by positivity
      linarith [hg.2.2.1]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (gamma16_fourth_le_envelope hφ)
      (show 0 ≤ (convolutionCoeff W d : ℝ) / (d * log (Q / d)) by dsimp [Q]; positivity)
  calc
    _ ≤ ((N : ℝ) * E * A) * (K * wuSingularSeries N / log N) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = (E * K) * ((N : ℝ) / log N) * (wuSingularSeries N * A) := by ring
    _ ≤ (E * K) * ((N : ℝ) / log N) * U :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (E * K) * ((1 + τ) * logarithmicIntegral N) * U := by gcongr
    _ = _ := by dsimp [boxTheta, E, U, Q, W]; ring

theorem gamma16_X_scaled (k : ℕ) {δ K τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hK : 0 ≤ K) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        let W := convolutionWuWindows N Δ V
        gamma16X N δ W * (K * wuSingularSeries N / log N) ≤
          (((1 + τ) * K / 4 * gamma16FourthIntegralEnvelope) + ε * K / 2) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  obtain ⟨TM, hTM4, hTM⟩ := gamma16_X_main k hδ hδhi hε
  obtain ⟨TL, _, hTL⟩ := omega3X_trueLi_sharp_lower hτ
  refine ⟨max TM TL, hTM4.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := hTM4.trans ((le_max_left _ _).trans hN)
  have hC := (wuSingularSeries_pos N (by omega)).le
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm := hTM N ((le_max_left _ _).trans hN) i Δ V hb
  have hn := gamma16_integral_scaled hN4 hδ hδhi hb hK (hTL N ((le_max_right _ _).trans hN))
  have he := omega3X_scaled_error_le hN4 hδ hδhi hb hε.le hK
  dsimp only at hm hn he ⊢
  change gamma16X N δ (convolutionWuWindows N Δ V) ≤
    gamma16IntegralMain N δ (convolutionWuWindows N Δ V) +
      ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) at hm
  have hmul := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ K * wuSingularSeries N / log N by positivity)
  linarith only [hmul, hn, he]

end Wu2008DoubleSieve
