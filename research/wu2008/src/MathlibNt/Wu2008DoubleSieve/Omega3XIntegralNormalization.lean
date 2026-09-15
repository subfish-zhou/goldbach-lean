import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureSource
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabPayment

/-!
# Sharp Li normalization of the physical X integral

Wu04, TeX2250--2259. The elementary sharp lower estimate for the actual
integral from two suffices: `N/log N <= (1+tau) Li(N)` eventually.
The fixed-delta density factor is not replaced by eight.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem omega3X_trueLi_sharp_lower {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (N : ℝ) / log N ≤ (1 + τ) * logarithmicIntegral N := by
  obtain ⟨T, hT⟩ := exists_nat_ge (2 * (1 + τ) / τ)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hlarge : 2 * (1 + τ) / τ ≤ (N : ℝ) :=
    hT.trans (by exact_mod_cast (le_max_right 4 T).trans hN)
  have hpay := (div_le_iff₀ hτ).mp hlarge
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hbase := box_trueLi_sub_lower (le_refl (2 : ℝ))
    (show (2 : ℝ) ≤ N by exact_mod_cast (show 2 ≤ N by omega))
  have htwo : logarithmicIntegral 2 = 0 := by
    simp [logarithmicIntegral, MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral]
  rw [htwo, sub_zero] at hbase
  calc
    _ ≤ ((1 + τ) * ((N : ℝ) - 2)) / log N :=
      div_le_div_of_nonneg_right (by nlinarith) hlog.le
    _ = (1 + τ) * (((N : ℝ) - 2) / log N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by linarith)

theorem omega3XIntegralMain_le_envelope {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    let W := convolutionWuWindows N Δ V
    omega3XIntegralMain N δ s t W ≤
      (N : ℝ) * omega3XIntegralEnvelope s t *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) /
            ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
  dsimp only
  unfold omega3XIntegralMain
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hl := log_pos hg.2.1
  have he := (omega3XIntegral_source_le_envelope hN hδ hδhi hb hd hs hst ht).2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left he
    (show 0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) /
      ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) by positivity)

/-- The exact quotient logarithm and the full singular series are retained. -/
theorem omega3XIntegralMain_scaled_le {i k N : ℕ} {δ Δ s t K τ : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hK : 0 ≤ K)
    (hli : (N : ℝ) / log N ≤ (1 + τ) * logarithmicIntegral N) :
    let W := convolutionWuWindows N Δ V
    let Q := (N : ℝ) ^ (1 / 2 - δ)
    omega3XIntegralMain N δ s t W * (K * wuSingularSeries N / log N) ≤
      ((1 + τ) * K / 4 * omega3XIntegralEnvelope s t) * boxTheta N Q W := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let E := omega3XIntegralEnvelope s t
  let A := ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) / ((d : ℝ) * log (Q / d))
  let U := ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log (Q / d))
  have hN0 : 0 < N := by omega
  have hC0 := wuSingularSeries_pos N hN0
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hE : 0 ≤ E := (omega3XIntegralEnvelope_bounds hs hst ht).1
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
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (show (0 : ℝ) ≤ N / (2 * log N) by positivity).trans (box_trueLi_lower hN)
  have he := omega3XIntegralMain_le_envelope (by omega) hδ hδhi hb hs hst ht
  change omega3XIntegralMain N δ s t W ≤ (N : ℝ) * E * A at he
  calc
    _ ≤ ((N : ℝ) * E * A) * (K * wuSingularSeries N / log N) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = (E * K) * ((N : ℝ) / log N) * (wuSingularSeries N * A) := by ring
    _ ≤ (E * K) * ((N : ℝ) / log N) * U :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (E * K) * ((1 + τ) * logarithmicIntegral N) * U := by gcongr
    _ = _ := by dsimp [boxTheta, E, U, Q, W]; ring

/-- The sharp normalization slack is fixed before N and every source box. -/
theorem omega3XIntegralMain_scaled_uniform (k : ℕ) {δ K τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hK : 0 ≤ K) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3XIntegralMain N δ s t W * (K * wuSingularSeries N / log N) ≤
          ((1 + τ) * K / 4 * omega3XIntegralEnvelope s t) * boxTheta N Q W := by
  obtain ⟨T, hT4, hT⟩ := omega3X_trueLi_sharp_lower hτ
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  exact omega3XIntegralMain_scaled_le (hT4.trans hN) hδ hδhi hb hs hst ht hK (hT N hN)

end Wu2008DoubleSieve
