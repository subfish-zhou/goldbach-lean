import WR2GammaHighPublicationBudget
import WR2GammaHighNormalized

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem publication_radius : ∃ r : ℝ, 0 < r ∧ ∀ j : Fin 3,
    r ≤ Wu04RemainingStrongPaid.deltaRadius j := by
  refine ⟨min (Wu04RemainingStrongPaid.deltaRadius 0)
    (min (Wu04RemainingStrongPaid.deltaRadius 1) (Wu04RemainingStrongPaid.deltaRadius 2)),
    lt_min (Wu04RemainingStrongPaid.deltaRadius_pos 0)
      (lt_min (Wu04RemainingStrongPaid.deltaRadius_pos 1) (Wu04RemainingStrongPaid.deltaRadius_pos 2)), ?_⟩
  intro j
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem actual_count_publication_theta {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : ∀ j : Fin 3, δ ≤ Wu04RemainingStrongPaid.deltaRadius j) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      5*psiCount (j.castAdd 4) N ≤
        (5*(1-Wu04RemainingCore.publication j)+ε)*theta j N δ+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := actual_count_coupled_fixed hd hh he
  refine ⟨T,hT,?_⟩
  intro N hN hn j
  have hc := publication_coefficient j hd (hr j)
  have hg := row_analytic j
  have hA : wuUpperCoefficient (Wu04RemainingCore.row j).s = 1 :=
    jr1965F_normalized_initial (by linarith [hg.two_lt_s]) hg.s_le_three
  rw [hA] at hc
  have hp := mul_le_mul_of_nonneg_right (add_le_add hc (le_refl ε))
    (theta_nonneg (N := N) j (by omega) hd hh)
  exact (h N hN hn j).trans (add_le_add hp le_rfl)

theorem actual_count_publication_original {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
        5*psiCount (j.castAdd 4) N ≤
          (8*psiLogWeight (j.castAdd 4)*(5*(1-Wu04RemainingCore.publication j))+ε)*truncatedSixthMassScale N := by
  let K : ℝ := ∑ j : Fin 3, |(5*(1-Wu04RemainingCore.publication j))|
  have hK : 0 ≤ K := sum_nonneg (fun _ _ => abs_nonneg _)
  have hKj (j : Fin 3) : |(5*(1-Wu04RemainingCore.publication j))| ≤ K :=
    single_le_sum (fun i _ => abs_nonneg ((5*(1-Wu04RemainingCore.publication i)))) (mem_univ j)
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
  obtain ⟨rpub,hrpub,hpub⟩ := publication_radius
  refine ⟨min r rpub, lt_min hr hrpub, (min_le_left _ _).trans hrhi, ?_⟩
  intro δ hd hdr
  have hdr0 : δ < r := hdr.trans_le (min_le_left _ _)
  have hrp : ∀ j : Fin 3, δ ≤ Wu04RemainingStrongPaid.deltaRadius j :=
    fun j => (hdr.le.trans (min_le_right _ _)).trans (hpub j)
  have hh : δ ≤ 1/100 := hdr0.le.trans hrhi
  obtain ⟨T2, _, hactual⟩ := actual_count_publication_theta hd hh hrp heta
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have hN4 : 4 ≤ N := by omega
  have hM := truncatedSixthClosure_scale_nonneg hN4
  have hn := hnorm δ hd hdr0 N (by omega) he j
  have ht := (abs_le.mp (htheta N (by omega) he j δ hd.le hh)).2
  have hb : theta j N δ ≤ 161*truncatedSixthMassScale N := by
    have hI := mul_le_mul_of_nonneg_right (prime_integral_bounds j hh).2 hM
    have hη := mul_le_mul_of_nonneg_right heta1 hM
    linarith
  have hc :
      (5*(1-Wu04RemainingCore.publication j))*(theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N) ≤
        K*η*truncatedSixthMassScale N := by
    calc
      _ ≤ |(5*(1-Wu04RemainingCore.publication j))*(theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N)| :=
        le_abs_self _
      _ = |(5*(1-Wu04RemainingCore.publication j))| * |theta j N δ-8*psiLogWeight (j.castAdd 4)*truncatedSixthMassScale N| :=
        abs_mul _ _
      _ ≤ |(5*(1-Wu04RemainingCore.publication j))| * (η*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg _)
      _ ≤ K*(η*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_right (hKj j) (mul_nonneg heta.le hM)
      _ = _ := by ring
  have ha := hactual N (by omega) he j
  have hb' := mul_le_mul_of_nonneg_left hb heta.le
  have hp := mul_le_mul_of_nonneg_right hpay hM
  nlinarith only [hc, ha, hb', hp]

theorem actual_three_publications {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      psiCount (j.castAdd 4) N ≤
        (8*psiLogWeight (j.castAdd 4)*(1-Wu04RemainingCore.publication j)+ε)*
          truncatedSixthMassScale N := by
  obtain ⟨r,hr,_,h⟩ := actual_count_publication_original (show 0 < 5*ε by positivity)
  obtain ⟨T,hT,hcount⟩ := h (r/2) (half_pos hr) (half_lt_self hr)
  refine ⟨T,hT,?_⟩
  intro N hN hn j
  have hc := hcount N hN hn j
  linarith only [hc]

end WuPaper.R2GammaHigh
#print axioms WuPaper.R2GammaHigh.actual_count_publication_original
