import Wu18938Campaign.M1.Confirmed.ClassicalLeaves
import MathlibNt.Wu2008DoubleSieve.CanonicalUpperExtension

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem roughBox_upper_main_four (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 4 →
      convolutionRosserMain N (convolutionWuWindows N Δ V) true
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
        (wuUpperCoefficient s + 6 * ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let ρ := exp eulerMascheroniConstant * ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Z,hdensity⟩ := ordinaryRosser_upper_density_canonical_extended_local hρ
  obtain ⟨T0,hT04,hcut⟩ := roughBox_cutoff_large m hη hδ (max Z 2)
  obtain ⟨T1,_,hlocal⟩ := roughBox_local_normalization m hη hδ he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s hs hs4
  have hN2 : 2 ≤ N := by omega
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by exact_mod_cast hN2)
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      ordinaryRosserMainSum true N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) ≤
        (wuUpperCoefficient s + 6 * ε) *
          (4 * wuSingularSeries (d * N) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
    have hg := hb.support_geometry hN2 hη hδ hd
    have hz := hcut N (by omega) i Δ V hb d hd s hs1 (by linarith)
    have hv := variableRosser_geometry hg.2.2.1 hs1
    have hden := hdensity N d heven (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hg.2.2.1]) hv.2.2.symm hs hs4
    have hnorm := hlocal N (by omega) heven i Δ V hb d hd s hs1 (by linarith)
    have hC := wuSingularSeries_pos (d * N) (Nat.mul_pos hg.1 (by omega))
    have hl := log_pos hg.2.2.1
    have hmpos : 0 < 2 * s * wuSingularSeries (d * N) /
        (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by positivity
    have hprod : localSieveProduct (d * N) (wuLocalCutoff N δ d s) ≤
        (1 + ε) * (2 * s * wuSingularSeries (d * N) /
          (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d))) := by
      apply (div_le_iff₀ hmpos).mp
      linarith [(abs_le.mp hnorm).2]
    have hF : 0 ≤ jr1965F s + ρ := add_nonneg (jr1965F_pos hs0).le hρ.le
    exact hden.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
      (canonical_upper_extended_normalization_budget hs1 hs4 hC.le hl he.le he1))
  unfold convolutionRosserMain boxTheta
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

theorem roughBox_upper_leaf_four (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 4 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (wuUpperCoefficient s + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 7)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 7 := min_le_right _ _
  obtain ⟨T0,hT04,hmain⟩ := roughBox_upper_main_four m hη hδ hτ hτ1
  obtain ⟨T1,_,hrem⟩ := roughBox_rosser_remainder m hη hδ hτ
  obtain ⟨T2,_,hbase⟩ := roughBox_upper_leaf m hη hδ he
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s hs hs4
  by_cases hslo : 3 / 2 ≤ s
  · have hM := hmain N (by omega) heven i Δ V hb s hslo hs4
    have hR := hrem N (by omega) i Δ V hb true (fun d => wuLocalCutoff N δ d s)
    have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
      nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hR) hτ
    have hfinite : wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        convolutionRosserMain N (convolutionWuWindows N Δ V) true
          (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) +
        convolutionRosserRemainder N (convolutionWuWindows N Δ V) true
          (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) := by
      unfold wuBoxPhi convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro d hd
      have hv := variableRosser_geometry (hb.support_geometry (by omega) hη hδ hd).2.2.1 hs
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (ordinaryRosser_upper_finite hv.1 hv.2.1) (Nat.cast_nonneg _)
    have hpay := mul_le_mul_of_nonneg_right (show 7 * τ ≤ ε by linarith) hθ
    have hr := (le_abs_self _).trans hR
    nlinarith only [hfinite,hM,hr,hpay]
  · have hs3 : s ≤ 3 := by linarith
    have ha : wuUpperCoefficient s = 1 := jr1965F_normalized_initial (by linarith) hs3
    rw [ha]
    exact hbase N (by omega) heven i Δ V hb s hs hs3

end Wu18938Campaign.M1.Confirmed
