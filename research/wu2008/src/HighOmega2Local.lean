import HighCrossOmega2
import MathlibNt.Wu2008DoubleSieve.PhiLower

namespace HighOmega2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
noncomputable section

/-- A total-product gap, not a squared-prefix hypothesis, makes the actual
local Euler product uniform in every supported modulus and cutoff. -/
theorem local_normalization {δ η ε : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η) → ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      |localSieveProduct (d*N) (wuLocalCutoff N δ d s) /
        (2*s*wuSingularSeries (d*N) /
          (exp eulerMascheroniConstant * log ((N : ℝ)^(1/2-δ)/d))) - 1| ≤ ε := by
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2/η) ε (by positivity) hε)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max Z 3)))
  refine ⟨max 2 T,le_max_left _ _,?_⟩
  intro N hN he d hd hsize s hs hs10
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcut := cutoff_lower hN2 hd hη (show 0 < s by linarith) hs10 hsize
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hcut
  have hdN : (d : ℝ) ≤ N := by
    apply hsize.trans
    calc
      _ ≤ (N : ℝ)^(1 : ℝ) := rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = _ := rpow_one _
  have hpoly : ((d*N : ℕ) : ℝ) ≤ (wuLocalCutoff N δ d s)^(2/η) := by
    calc
      _ ≤ (N : ℝ)^(2 : ℝ) := by
        rw [Nat.cast_mul,rpow_two,pow_two]
        exact mul_le_mul_of_nonneg_right hdN hNr.le
      _ = ((N : ℝ)^η)^(2/η) := by
        rw [← rpow_mul hNr.le]
        congr 1
        field_simp
      _ ≤ _ := rpow_le_rpow (by positivity) hcut (by positivity)
  have hr := hZ _ ((le_max_left _ _).trans hlarge) (d*N)
    (Nat.mul_pos hd (by omega)) (he.mul_left d) hpoly
  have hq : 0 < (N : ℝ)^(1/2-δ)/d := div_pos (rpow_pos_of_pos hNr _) (by exact_mod_cast hd)
  have hlog : log (wuLocalCutoff N δ d s) = (1/s)*log ((N : ℝ)^(1/2-δ)/d) := log_rpow hq _
  have hs0 : s ≠ 0 := by linarith
  have hmain : 2*exp (-eulerMascheroniConstant)*wuSingularSeries (d*N) /
      log (wuLocalCutoff N δ d s) = 2*s*wuSingularSeries (d*N) /
        (exp eulerMascheroniConstant*log ((N : ℝ)^(1/2-δ)/d)) := by
    rw [hlog,exp_neg]
    field_simp
  rwa [hmain] at hr

/-- Simultaneous lower and upper canonical main masses on any prime box
with total slack. No Uk admissibility or H/h is used. -/
theorem main_normalization {δ η ε : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ i : ℕ,
      ∀ W : Fin i → Finset ℕ, (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      (∀ s : ℝ, 2 ≤ s → s ≤ 4 →
        (log (s-1)-4*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W ≤
          convolutionRosserMain N W false (wuVariableRosserLevel N δ)
            (fun d => wuLocalCutoff N δ d s)) ∧
      (∀ s : ℝ, 3/2 ≤ s → s ≤ 3 →
        convolutionRosserMain N W true (wuVariableRosserLevel N δ)
          (fun d => wuLocalCutoff N δ d s) ≤
            (1+ε)^2*boxTheta N ((N : ℝ)^(1/2-δ)) W) := by
  obtain ⟨ZL,hL⟩ := ordinaryRosser_lower_density_canonical_local
    (show 0 < exp eulerMascheroniConstant*ε/2 by positivity)
  obtain ⟨ZU,hU⟩ := ordinaryRosser_upper_density_canonical
    (show 0 < 2*exp eulerMascheroniConstant*ε/3 by positivity)
  obtain ⟨T0,hT02,hlocal⟩ := local_normalization hδ hη hε
  obtain ⟨T1,hT1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 2 (max ZL ZU))))
  refine ⟨max T0 T1,hT02.trans (le_max_left _ _),?_⟩
  intro N hN he i W hW hsize
  have hN0 := (le_max_left T0 T1).trans hN
  have hN2 := hT02.trans hN0
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hli : 0 ≤ AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num) (by exact_mod_cast hN2)
  have hg : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ 1 < (N : ℝ)^(1/2-δ)/d := by
    intro d hd
    have hd0 := boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
    refine ⟨hd0,(one_lt_div (by exact_mod_cast hd0)).mpr ?_⟩
    exact (hsize d hd).trans_lt (rpow_lt_rpow_of_exponent_lt hNr (by linarith))
  have hz : ∀ d ∈ boxConvolutionSupport W, ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      max 2 (max ZL ZU) ≤ wuLocalCutoff N δ d s := by
    intro d hd s hs hs10
    exact (hT1 N ((le_max_right _ _).trans hN)).trans
      (cutoff_lower hN2 (hg d hd).1 hη (by linarith) hs10 (hsize d hd))
  constructor
  · intro s hs hs4
    have hp : ∀ d ∈ boxConvolutionSupport W,
        (log (s-1)-4*ε)*(4*wuSingularSeries (d*N)/log ((N : ℝ)^(1/2-δ)/d)) ≤
          ordinaryRosserMainSum false N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) := by
      intro d hd
      have hq := (hg d hd).2
      have hz' := hz d hd s (by linarith) (by linarith)
      have hl := hL N d he _ _ s
        ((le_max_left ZL ZU).trans ((le_max_right _ _).trans hz'))
        ((le_max_left _ _).trans hz') (by linarith)
        (log_div_log_rpow_eq hq (by linarith)).symm hs hs4
      exact (canonical_lower_normalization_budget hs hs4
        (wuSingularSeries_pos _ (Nat.mul_pos (hg d hd).1 (by omega)))
        (log_pos hq) hε.le hε1
        (hlocal N hN0 he d (hg d hd).1 (hsize d hd) s (by linarith) (by linarith))).trans hl
    unfold boxTheta convolutionRosserMain
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro d hd
    have h := mul_le_mul_of_nonneg_left (hp d hd)
      (mul_nonneg (Nat.cast_nonneg (convolutionCoeff W d)) (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
    convert h using 1 <;> ring
  · intro s hs hs3
    have hp : ∀ d ∈ boxConvolutionSupport W,
        ordinaryRosserMainSum true N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) ≤
          (1+ε)^2*(4*wuSingularSeries (d*N)/log ((N : ℝ)^(1/2-δ)/d)) := by
      intro d hd
      have hq := (hg d hd).2
      have hz' := hz d hd s (by linarith) (by linarith)
      have hu := hU N d he _ _ s
        ((le_max_right ZL ZU).trans ((le_max_right _ _).trans hz'))
        ((le_max_left _ _).trans hz') (by linarith)
        (log_div_log_rpow_eq hq (by linarith)).symm hs hs3
      have heuler : (∏ p ∈ primeWindow (d*N) 0 (wuLocalCutoff N δ d s),
          (1-1/((p : ℝ)-1))) = localSieveProduct (d*N) (wuLocalCutoff N δ d s) := by
        rw [localSieveProduct,localSievePrimes_eq_primeWindow]
      rw [heuler] at hu
      have hn := hlocal N hN0 he d (hg d hd).1 (hsize d hd) s (by linarith) (by linarith)
      have hC := wuSingularSeries_pos _ (Nat.mul_pos (hg d hd).1 (show 0 < N by omega))
      have hM : 0 < 2*s*wuSingularSeries (d*N)/(exp eulerMascheroniConstant*log ((N : ℝ)^(1/2-δ)/d)) := by
        have := log_pos hq
        have hs0 : 0 < s := by linarith
        positivity
      have hv : localSieveProduct (d*N) (wuLocalCutoff N δ d s) ≤
          (1+ε)*(2*s*wuSingularSeries (d*N)/(exp eulerMascheroniConstant*log ((N : ℝ)^(1/2-δ)/d))) := by
        apply (div_le_iff₀ hM).mp
        linarith [(abs_le.mp hn).2]
      have hF : 0 ≤ MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F s +
          2*exp eulerMascheroniConstant*ε/3 := by
        rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three hs3]
        have hs0 : 0 < s := by linarith
        positivity
      exact hu.trans ((mul_le_mul_of_nonneg_left hv hF).trans
        (canonical_upper_normalization_budget (by linarith) hs3 hC.le (log_pos hq) hε.le))
    unfold convolutionRosserMain boxTheta
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro d hd
    have h := mul_le_mul_of_nonneg_left (hp d hd)
      (mul_nonneg (Nat.cast_nonneg (convolutionCoeff W d)) (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
    convert h using 1 <;> ring

end
end HighOmega2
