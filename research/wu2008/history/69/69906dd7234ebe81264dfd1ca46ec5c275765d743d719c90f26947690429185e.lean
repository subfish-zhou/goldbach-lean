import R2GammaHighSignedEight

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem classical_coefficient_original (j : Fin 3) :
    classicalEight j = 5*(1-classicalGain j) := by
  rw [classical_coefficient_identity]
  have hg := row_analytic j
  have hA : wuUpperCoefficient (Wu04RemainingCore.row j).s = 1 :=
    jr1965F_normalized_initial (by linarith [hg.two_lt_s]) hg.s_le_three
  rw [hA]

theorem theta_original_error {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧ ∃ T : ℕ, 4 ≤ T ∧
      ∀ δ : ℝ, 0 < δ → δ < r → ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
        |theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N| ≤
          ε*truncatedSixthMassScale N := by
  obtain ⟨r, hr, hrhi, hnear⟩ := common_delta_radius (show 0 < ε/2 by positivity)
  obtain ⟨T, hT4, htheta⟩ := theta_integral_error (show 0 < ε/2 by positivity)
  refine ⟨r, hr, hrhi, T, hT4, ?_⟩
  intro δ hd hdr N hN he j
  have hM := truncatedSixthClosure_scale_nonneg (hT4.trans hN)
  have ht := htheta N hN he j δ hd.le (hdr.le.trans hrhi)
  have hc := mul_le_mul_of_nonneg_right (hnear δ hd hdr j).le hM
  have ht' :
      |4*primeIntegral j δ*truncatedSixthMassScale N -
        8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N| ≤ ε/2*truncatedSixthMassScale N := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hM]
    exact hc
  have h := (abs_add (theta j N δ-4*primeIntegral j δ*truncatedSixthMassScale N)
    (4*primeIntegral j δ*truncatedSixthMassScale N -
      8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N)).trans (add_le_add ht ht')
  convert h using 1 <;> ring

theorem signed_eight_normalized {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
        signedEight j N δ ≤
          (8*psiLogWeight (j.castAdd 4)*classicalEight j+ε)*truncatedSixthMassScale N := by
  let K : ℝ := ∑ j : Fin 3, |classicalEight j|
  have hK : 0 ≤ K := sum_nonneg (fun _ _ => abs_nonneg _)
  have hKj (j : Fin 3) : |classicalEight j| ≤ K :=
    single_le_sum (fun i _ => abs_nonneg (classicalEight i)) (mem_univ j)
  let η : ℝ := min 1 (ε/(K+163))
  have heta : 0 < η := lt_min (by norm_num) (by positivity)
  have heta1 : η ≤ 1 := min_le_left _ _
  have hpay : (K+162)*η ≤ ε := by
    have h := (le_div_iff₀ (show 0 < K+163 by positivity)).mp
      (min_le_right 1 (ε/(K+163)))
    change η*(K+163) ≤ ε at h
    nlinarith
  obtain ⟨r, hr, hrhi, T0, hT04, hnorm⟩ := theta_original_error heta
  obtain ⟨T1, _, htheta⟩ := theta_integral_error heta
  refine ⟨r, hr, hrhi, ?_⟩
  intro δ hd hdr
  have hh : δ ≤ 1/100 := hdr.le.trans hrhi
  obtain ⟨T2, _, hactual⟩ := signed_eight_actual_upper hd hh heta
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have hN4 : 4 ≤ N := by omega
  have hM := truncatedSixthClosure_scale_nonneg hN4
  have hn := hnorm δ hd hdr N (by omega) he j
  have ht := (abs_le.mp (htheta N (by omega) he j δ hd.le hh)).2
  have hb : theta j N δ ≤ 161*truncatedSixthMassScale N := by
    have hI := mul_le_mul_of_nonneg_right (prime_integral_bounds j hh).2 hM
    have hη := mul_le_mul_of_nonneg_right heta1 hM
    linarith
  have hc :
      classicalEight j*(theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N) ≤
        K*η*truncatedSixthMassScale N := by
    calc
      _ ≤ |classicalEight j*(theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N)| :=
        le_abs_self _
      _ = |classicalEight j|*|theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N| :=
        abs_mul _ _
      _ ≤ |classicalEight j|*(η*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg _)
      _ ≤ K*(η*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_right (hKj j) (mul_nonneg heta.le hM)
      _ = _ := by ring
  have ha := hactual N (by omega) he j
  have hb' := mul_le_mul_of_nonneg_left hb heta.le
  have hp := mul_le_mul_of_nonneg_right hpay hM
  nlinarith only [hc, ha, hb', hp]

theorem actual_count_partial_original {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
        psiCount (j.castAdd 4) N ≤
          (8*psiLogWeight (j.castAdd 4)*(1-classicalGain j)+ε)*truncatedSixthMassScale N +
            unpaidThirteen j N δ/5 := by
  obtain ⟨r, hr, hrhi, h⟩ := signed_eight_normalized (show 0 < 5*ε by positivity)
  refine ⟨r, hr, hrhi, ?_⟩
  intro δ hd hdr
  obtain ⟨T, hT4, hN⟩ := h δ hd hdr
  refine ⟨T, hT4, ?_⟩
  intro N hNT he j
  have hf := coupled_high_actual_finite j (by omega : 2 ≤ N) hd (hdr.le.trans hrhi)
  change _ ≤ secondFunctionalMotherRHS _ N δ (windows j N) at hf
  rw [mother_split_eight_thirteen] at hf
  have hpaid := hN N hNT he j
  rw [classical_coefficient_original] at hpaid
  linarith only [hf, hpaid]

#check @classical_coefficient_original
#check @theta_original_error
#check @signed_eight_normalized
#check @actual_count_partial_original
#print axioms classical_coefficient_original
#print axioms theta_original_error
#print axioms signed_eight_normalized
#print axioms actual_count_partial_original
end WuPaper.R2GammaHigh
