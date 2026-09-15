import HighOmega2Local
import MathlibNt.Wu2008DoubleSieve.CanonicalBoundedDensity
import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies

namespace HighFull
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Topology
noncomputable section

/-- Actual full-range Rosser main mass on total-product slack. The coefficient
is the genuine A(s), including beyond three; the threshold precedes all boxes. -/
theorem main_upper {δ η ε : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ i : ℕ,
      ∀ W : Fin i → Finset ℕ, (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s : ℝ, 3/2 ≤ s → s ≤ 10 →
        convolutionRosserMain N W true (wuVariableRosserLevel N δ)
          (fun d => wuLocalCutoff N δ d s) ≤
        (wuUpperCoefficient s+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  let e := min 1 (ε/15)
  have he0 : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heε : 15*e ≤ ε := by have := min_le_right (1 : ℝ) (ε/15); dsimp [e]; linarith
  obtain ⟨Z,hU⟩ := ordinaryRosser_upper_density_canonical_bounded_local
    (show 0 < exp eulerMascheroniConstant*e/2 by positivity)
  obtain ⟨T0,hT02,hlocal⟩ := HighOmega2.local_normalization hδ hη he0
  obtain ⟨T1,hT1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 2 Z)))
  refine ⟨max T0 T1,hT02.trans (le_max_left _ _),?_⟩
  intro N hN he i W hW hsize s hs hs10
  have hN0 := (le_max_left T0 T1).trans hN
  have hN2 := hT02.trans hN0
  have hg := HighCross.support_admission W hN2 hη hW hsize
  have hli : 0 ≤ AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num) (by exact_mod_cast hN2)
  have hp : ∀ d ∈ boxConvolutionSupport W,
      ordinaryRosserMainSum true N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) ≤
      (wuUpperCoefficient s+ε)*(4*wuSingularSeries (d*N)/log ((N : ℝ)^(1/2-δ)/d)) := by
    intro d hd
    have hq := hg.2 d hd
    have hz := (hT1 N ((le_max_right _ _).trans hN)).trans
      (cutoff_lower hN2 (hg.1 d hd) hη (by linarith) hs10 (hsize d hd))
    have hu := hU N d he _ _ s ((le_max_right _ _).trans hz)
      ((le_max_left _ _).trans hz) (by linarith)
      (log_div_log_rpow_eq hq (by linarith)).symm hs hs10
    have hn := hlocal N hN0 he d (hg.1 d hd) (hsize d hd) s (by linarith) hs10
    have hC := wuSingularSeries_pos _ (Nat.mul_pos (hg.1 d hd) (show 0 < N by omega))
    have hl := log_pos hq
    have hs0 : 0 < s := by linarith
    have hM : 0 < 2*s*wuSingularSeries (d*N)/(exp eulerMascheroniConstant*log ((N : ℝ)^(1/2-δ)/d)) := by
      positivity
    have hv : localSieveProduct (d*N) (wuLocalCutoff N δ d s) ≤
        (1+e)*(2*s*wuSingularSeries (d*N)/(exp eulerMascheroniConstant*log ((N : ℝ)^(1/2-δ)/d))) := by
      apply (div_le_iff₀ hM).mp
      linarith [(abs_le.mp hn).2]
    have hF : 0 ≤ jr1965F s+exp eulerMascheroniConstant*e/2 :=
      add_nonneg (jr1965F_pos hs0).le (by positivity)
    have hb := canonical_upper_bounded_normalization_budget (by linarith : 1 ≤ s) hs10 hC.le hl he0.le he1
    change _ ≤ (wuUpperCoefficient s+15*e)*(4*wuSingularSeries (d*N)/log ((N : ℝ)^(1/2-δ)/d)) at hb
    exact hu.trans ((mul_le_mul_of_nonneg_left hv hF).trans (hb.trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))))
  unfold convolutionRosserMain boxTheta
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hp d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff W d)) (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

end
end HighFull
