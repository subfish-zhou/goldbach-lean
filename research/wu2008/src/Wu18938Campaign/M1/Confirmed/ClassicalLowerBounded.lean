import Wu18938Campaign.M1.Confirmed.ClassicalBounded

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem roughBox_lower_main_bounded (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 10 →
      (wuLowerCoefficient s - 15 * ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      convolutionRosserMain N (convolutionWuWindows N Δ V) false
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) := by
  obtain ⟨Z,hdensity⟩ := ordinaryRosser_lower_density_canonical_bounded_local
    (show 0 < exp eulerMascheroniConstant * ε / 2 by positivity)
  obtain ⟨T0,hT04,hcut⟩ := roughBox_cutoff_large m hη hδ (max Z 2)
  obtain ⟨T1,_,hlocal⟩ := roughBox_local_normalization m hη hδ he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s hs hs10
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by
      exact_mod_cast (show 2 ≤ N by omega))
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (wuLowerCoefficient s - 15 * ε) * (4 * wuSingularSeries (d * N) /
        log ((N : ℝ) ^ (1 / 2 - δ) / d)) ≤
      ordinaryRosserMainSum false N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) := by
    have hg := hb.support_geometry (by omega) hη hδ hd
    have hz := hcut N (by omega) i Δ V hb d hd s (by linarith) hs10
    have hv := variableRosser_geometry hg.2.2.1 (by linarith : 1 ≤ s)
    have hden := hdensity N d heven (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hg.2.2.1]) hv.2.2.symm hs hs10
    have hnorm := hlocal N (by omega) heven i Δ V hb d hd s (by linarith) hs10
    exact (canonical_lower_bounded_normalization_budget hs hs10
      (wuSingularSeries_pos (d * N) (Nat.mul_pos hg.1 (by omega)))
      (log_pos hg.2.2.1) he.le he1 hnorm).trans hden
  unfold boxTheta convolutionRosserMain
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

theorem roughBox_lower_leaf_bounded (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      (wuLowerCoefficient s - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  let τ := min 1 (ε / 16)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : 16 * τ ≤ ε := by have hh := min_le_right 1 (ε / 16); change τ ≤ ε / 16 at hh; linarith
  obtain ⟨T0,hT04,hmain⟩ := roughBox_lower_main_bounded m hη hδ hτ hτ1
  obtain ⟨T1,_,hrem⟩ := roughBox_rosser_remainder m hη hδ hτ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s hs hs10
  have hR := hrem N (by omega) i Δ V hb false (fun d => wuLocalCutoff N δ d s)
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hR) hτ
  by_cases hs2 : s ≤ 2
  · rw [wuLowerCoefficient,jr1965f_initial hs2,mul_zero,zero_div,zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hθ).trans (wuBoxPhi_nonneg N δ _ s)
  have hM := hmain N (by omega) heven i Δ V hb s (lt_of_not_ge hs2).le hs10
  have hfinite : convolutionRosserMain N (convolutionWuWindows N Δ V) false
      (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) +
      convolutionRosserRemainder N (convolutionWuWindows N Δ V) false
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
    unfold wuBoxPhi convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hv := variableRosser_geometry (hb.support_geometry (by omega) hη hδ hd).2.2.1 hs
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (ordinaryRosser_lower_finite hv.2.1) (Nat.cast_nonneg _)
  have hr := (abs_le.mp hR).1
  have hp := mul_le_mul_of_nonneg_right hτε hθ
  nlinarith only [hfinite,hM,hr,hp]

end Wu18938Campaign.M1.Confirmed
