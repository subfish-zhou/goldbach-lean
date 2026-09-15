import Wu18938Campaign.M1.Confirmed.HighPair

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real Filter
open scoped Classical Topology

theorem roughBox_cutoff_lower {m i N d : ℕ} {η δ Δ s : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    (N : ℝ) ^ (η / 10) ≤ wuLocalCutoff N δ d s := by
  have hs0 : 0 < s := by linarith
  have hp := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) (hb.remaining d hd)
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have he : (N : ℝ) ^ (η / 10) ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / 10 : ℝ) := by
    simpa only [← rpow_mul (Nat.cast_nonneg N), div_eq_mul_inv, one_mul] using hp
  exact he.trans (rpow_le_rpow_of_exponent_le
    (hb.support_geometry hN hη hδ hd).2.2.1.le (one_div_le_one_div_of_le hs0 hs10))

theorem roughBox_cutoff_large (m : ℕ) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (Z : ℝ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 → Z ≤ wuLocalCutoff N δ d s := by
  obtain ⟨T, ht⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < η / 10 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop Z))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd s hs hs10
  exact (ht N (by omega)).trans (roughBox_cutoff_lower hb (by omega) hη hδ hd hs hs10)

theorem roughBox_local_normalization (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      |localSieveProduct (d * N) (wuLocalCutoff N δ d s) /
        (2 * s * wuSingularSeries (d * N) /
          (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d))) - 1| ≤ ε := by
  let α := η / 10
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2 / α) ε (by positivity) he)
  obtain ⟨T, hT4, ht⟩ := roughBox_cutoff_large m hη hδ (max Z 3)
  refine ⟨T, hT4, ?_⟩
  intro N hN heven i Δ V hb d hd s hs hs10
  have hN2 : 2 ≤ N := by omega
  have hg := hb.support_geometry hN2 hη hδ hd
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut := roughBox_cutoff_lower hb hN2 hη hδ hd hs hs10
  have hz := ht N hN i Δ V hb d hd s hs hs10
  have hpoly : ((d * N : ℕ) : ℝ) ≤ wuLocalCutoff N δ d s ^ (2 / α) := by
    calc
      _ ≤ (N : ℝ) ^ (2 : ℝ) := by
        rw [Nat.cast_mul, rpow_two, pow_two]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hg.2.1) hNr.le
      _ = ((N : ℝ) ^ α) ^ (2 / α) := by
        rw [← rpow_mul hNr.le]
        congr 1
        field_simp
      _ ≤ _ := rpow_le_rpow (by positivity) hcut (by positivity)
  have hrel := hZ _ ((le_max_left _ _).trans hz) (d * N)
    (Nat.mul_pos hg.1 (by omega)) (heven.mul_left d) hpoly
  have hs0 : s ≠ 0 := by linarith
  have hlog : log (wuLocalCutoff N δ d s) =
      (1 / s) * log ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    log_rpow (by linarith [hg.2.2.1]) _
  have hlq := (log_pos hg.2.2.1).ne'
  have hmain : 2 * exp (-eulerMascheroniConstant) * wuSingularSeries (d * N) /
      log (wuLocalCutoff N δ d s) =
      2 * s * wuSingularSeries (d * N) /
        (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
    rw [hlog, exp_neg]
    field_simp
  rwa [hmain] at hrel

theorem roughBox_rosser_remainder (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ upper : Bool, ∀ z : ℕ → ℝ,
      |convolutionRosserRemainder N (convolutionWuWindows N Δ V)
        upper (wuVariableRosserLevel N δ) z| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T0, hBV⟩ := convolution_bombieri_vinogradov m hη hδ
    (show (0 : ℝ) < (5 * m + 3 : ℕ) by positivity)
  obtain ⟨c, hc, T1, hT14, hTheta⟩ := roughBox_theta_lower m hη hδ
  obtain ⟨T2, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max T1 (max T0 T2), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb upper z
  have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  have hB := hBV N (by omega) i hb.depth (convolutionWuWindows N Δ V) (by
    intro j q hq
    exact ⟨(hb.window_large j q hq).1, (mem_convolutionWuWindows.mp hq).2.1,
      (hb.window_large j q hq).2⟩)
  rw [rpow_natCast] at hB
  have hT := hTheta N (by omega) i Δ V hb
  have hbudget : C / log (N : ℝ) ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos he hc)).mp (hlogT N (by omega))
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ convolutionAPError N (convolutionModulusCutoff N δ) (convolutionWuWindows N Δ V) :=
      convolutionRosserRemainder_le_AP _ upper _ z
        (fun d _ => (wuVariableRosserLevel_eq_combined N d δ).le)
    _ ≤ C * N / log (N : ℝ) ^ (5 * m + 3) := hB
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by
      rw [show 5 * m + 3 = (5 * m + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hT he.le

end Wu18938Campaign.M1.Confirmed
