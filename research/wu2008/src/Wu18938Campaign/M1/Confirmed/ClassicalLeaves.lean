import Wu18938Campaign.M1.Confirmed.ClassicalInputs
import MathlibNt.Wu2008DoubleSieve.PhiLower

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem roughBox_upper_main (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 3 →
      convolutionRosserMain N (convolutionWuWindows N Δ V) true
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
        (1 + ε) ^ 2 * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let ρ := 2 * exp eulerMascheroniConstant * ε / 3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_upper_density_canonical hρ
  obtain ⟨T0, hT04, hcut⟩ := roughBox_cutoff_large m hη hδ (max Z 2)
  obtain ⟨T1, _, hlocal⟩ := roughBox_local_normalization m hη hδ he
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb s hs hs3
  have hN2 : 2 ≤ N := by omega
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by exact_mod_cast hN2)
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      ordinaryRosserMainSum true N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) ≤
        (1 + ε) ^ 2 * (4 * wuSingularSeries (d * N) /
          log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
    have hg := hb.support_geometry hN2 hη hδ hd
    have hz := hcut N (by omega) i Δ V hb d hd s hs1 (by linarith)
    have hv := variableRosser_geometry hg.2.2.1 hs1
    have hden := hdensity N d heven (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hg.2.2.1]) hv.2.2.symm hs hs3
    have heuler : (∏ q ∈ primeWindow (d * N) 0 (wuLocalCutoff N δ d s),
        (1 - 1 / ((q : ℝ) - 1))) = localSieveProduct (d * N) (wuLocalCutoff N δ d s) := by
      rw [localSieveProduct, localSievePrimes_eq_primeWindow]
    rw [heuler] at hden
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
    have hF : 0 ≤ jr1965F s + ρ := by rw [jr1965F_eq_of_le_three hs3]; positivity
    exact hden.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
      (canonical_upper_normalization_budget hs0 hs3 hC.le hl he.le))
  unfold convolutionRosserMain boxTheta
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

theorem roughBox_upper_leaf (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 3 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (1 + ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 4)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 4 := min_le_right _ _
  obtain ⟨T0, hT04, hmain⟩ := roughBox_upper_main m hη hδ hτ
  obtain ⟨T1, _, hrem⟩ := roughBox_rosser_remainder m hη hδ hτ
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb s hs hs3
  let t := max 2 s
  have ht : 3 / 2 ≤ t := (by norm_num : (3 / 2 : ℝ) ≤ 2).trans (le_max_left _ _)
  have ht3 : t ≤ 3 := max_le (by norm_num) hs3
  have hM := hmain N (by omega) heven i Δ V hb t ht ht3
  have hR := hrem N (by omega) i Δ V hb true (fun d => wuLocalCutoff N δ d t)
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hR) hτ
  have hfinite : wuBoxPhi N δ (convolutionWuWindows N Δ V) t ≤
      convolutionRosserMain N (convolutionWuWindows N Δ V) true
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d t) +
      convolutionRosserRemainder N (convolutionWuWindows N Δ V) true
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d t) := by
    unfold wuBoxPhi convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hv := variableRosser_geometry (hb.support_geometry (by omega) hη hδ hd).2.2.1
      (by linarith : 1 ≤ t)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (ordinaryRosser_upper_finite hv.1 hv.2.1) (Nat.cast_nonneg _)
  have hmono : wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) t := by
    unfold wuBoxPhi convolutionSieveCount
    apply sum_le_sum
    intro d hd
    exact mul_le_mul_of_nonneg_left
      (gamma5Classical_source_count_antitone N d (d * N)
        (hb.cutoff_antitone (by omega) hη hδ hd (by linarith) (le_max_right _ _)))
      (Nat.cast_nonneg _)
  have hbudget : (1 + τ) ^ 2 + τ ≤ 1 + ε := by
    nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hτ1)]
  have hpay := mul_le_mul_of_nonneg_right hbudget hθ
  have hr := (le_abs_self _).trans hR
  nlinarith only [hmono, hfinite, hM, hr, hpay]

theorem roughBox_lower_main (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
      (log (s - 1) - 4 * ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      convolutionRosserMain N (convolutionWuWindows N Δ V) false
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) := by
  let ρ := exp eulerMascheroniConstant * ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_lower_density_canonical_local hρ
  obtain ⟨T0, hT04, hcut⟩ := roughBox_cutoff_large m hη hδ (max Z 2)
  obtain ⟨T1, _, hlocal⟩ := roughBox_local_normalization m hη hδ he
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb s hs hs4
  have hN2 : 2 ≤ N := by omega
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by exact_mod_cast hN2)
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (log (s - 1) - 4 * ε) * (4 * wuSingularSeries (d * N) /
        log ((N : ℝ) ^ (1 / 2 - δ) / d)) ≤
      ordinaryRosserMainSum false N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) := by
    have hg := hb.support_geometry hN2 hη hδ hd
    have hz := hcut N (by omega) i Δ V hb d hd s (by linarith) (by linarith)
    have hv := variableRosser_geometry hg.2.2.1 (by linarith : 1 ≤ s)
    have hden := hdensity N d heven (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hg.2.2.1]) hv.2.2.symm hs hs4
    have hnorm := hlocal N (by omega) heven i Δ V hb d hd s (by linarith) (by linarith)
    exact (canonical_lower_normalization_budget hs hs4
      (wuSingularSeries_pos (d * N) (Nat.mul_pos hg.1 (by omega)))
      (log_pos hg.2.2.1) he.le he1 hnorm).trans hden
  unfold boxTheta convolutionRosserMain
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

theorem roughBox_lower_leaf (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 4 →
      (wuLowerCoefficient s - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  let τ := min 1 (ε / 5)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 5 := min_le_right _ _
  obtain ⟨T0, hT04, hmain⟩ := roughBox_lower_main m hη hδ hτ hτ1
  obtain ⟨T1, _, hrem⟩ := roughBox_rosser_remainder m hη hδ hτ
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb s hs hs4
  have hR := hrem N (by omega) i Δ V hb false (fun d => wuLocalCutoff N δ d s)
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hR) hτ
  by_cases hs2 : s ≤ 2
  · rw [wuLowerCoefficient, jr1965f_initial hs2, mul_zero, zero_div, zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hθ).trans (wuBoxPhi_nonneg N δ _ s)
  have hs2' : 2 ≤ s := (lt_of_not_ge hs2).le
  change (s * jr1965f s / (2 * exp eulerMascheroniConstant) - ε) * _ ≤ _
  rw [jr1965f_normalized_firstInterval hs2' hs4]
  have hM := hmain N (by omega) heven i Δ V hb s hs2' hs4
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
  have hr' := (abs_le.mp hR).1
  have hpay := mul_le_mul_of_nonneg_right (show 5 * τ ≤ ε by linarith) hθ
  nlinarith only [hfinite, hM, hr', hpay]

end Wu18938Campaign.M1.Confirmed
