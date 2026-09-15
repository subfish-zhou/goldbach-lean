import R2GammaHighGeometry

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighTheta HighBoxRecovery Real Finset Filter
open scoped Classical Topology

theorem ap_paid {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3,
        convolutionAPError N (convolutionModulusCutoff N δ) (windows j N) ≤
          C*N/log (N : ℝ)^(3 : ℝ) ∧
        convolutionAPError N (convolutionModulusCutoff N δ)
          (Fin.cons (HighO2Terminal.apPrimeCover N) (windows j N)) ≤
          C*N/log (N : ℝ)^(3 : ℝ) := by
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov 2
    (show 0 < highEta by norm_num [highEta]) hd (show (0 : ℝ) < 3 by norm_num)
  refine ⟨C, hC, max 4 T, le_max_left _ _, ?_⟩
  intro N hN j
  have hg : ∀ i d, d ∈ windows j N i →
      d.Prime ∧ d.Coprime N ∧ (N : ℝ)^highEta ≤ d := by
    intro i d hm
    have h := prime_geometry j (by omega) hd hh hm
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  constructor
  · exact hBV N (by omega) 1 (by norm_num) (windows j N) hg
  · apply hBV N (by omega) 2 le_rfl
    intro i p hp
    revert hp
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hp
      have h := mem_primeWindow.mp hp
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact hg i p

theorem ap_small {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      convolutionAPError N (convolutionModulusCutoff N δ) (windows j N) ≤
        ε * truncatedSixthMassScale N ∧
      convolutionAPError N (convolutionModulusCutoff N δ)
        (Fin.cons (HighO2Terminal.apPrimeCover N) (windows j N)) ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨C, hC, T, hT4, hAP⟩ := ap_paid hd hh
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max T M, hT4.trans (le_max_left _ _), ?_⟩
  intro N hN j
  have hN4 : 4 ≤ N := hT4.trans (by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C ≤ ε * wuSingularSeries N * log (N : ℝ) := by
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hM N (by omega))
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries heps.le) hlog.le)
  have hsmall : C*N/log (N : ℝ)^(3 : ℝ) ≤ ε*truncatedSixthMassScale N := by
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, rpow_natCast]
    unfold truncatedSixthMassScale
    apply (div_le_iff₀ (pow_pos hlog 3)).mpr
    have hw := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℝ) N)
    convert hw using 1 <;> field_simp <;> ring
  exact ⟨((hAP N (by omega) j).1).trans hsmall,
    ((hAP N (by omega) j).2).trans hsmall⟩

theorem phi_upper {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      ∀ s : ℝ, 3/2 ≤ s → s ≤ 10 →
        wuBoxPhi N δ (windows j N) s ≤
          (wuUpperCoefficient s + ε) * theta j N δ +
            ε * truncatedSixthMassScale N := by
  obtain ⟨T0, _, hmain⟩ := HighFull.main_upper hd.le
    (show 0 < highEta by norm_num [highEta]) heps
  obtain ⟨T1, hT14, hAP⟩ := ap_small hd hh heps
  refine ⟨max T0 T1, hT14.trans (le_max_right _ _), ?_⟩
  intro N hN he j s hs hs10
  have hN4 : 4 ≤ N := hT14.trans (by omega)
  have hsize := support_size j (by omega) hd hh
  have hp : ∀ i d, d ∈ windows j N i → d.Prime :=
    fun _ _ hm => (mem_primeWindow.mp hm).1
  have hmainN := hmain N (by omega) he 1 (windows j N) hp hsize s hs hs10
  have hq := (HighCross.support_admission (windows j N) (by omega)
    (show 0 < highEta by norm_num [highEta]) hp hsize).2
  exact (HighCross.rosser_upper (windows j N) hq (by linarith)).trans
    (add_le_add hmainN (hAP N (by omega) j).1)

theorem gamma_one_identity (j : Fin 3) (N : ℕ) (δ : ℝ) :
    gamma j N δ 1 =
      4 * wuBoxPhi N δ (windows j N) (Wu04RemainingCore.row j).S +
        wuBoxPhi N δ (windows j N) (Wu04RemainingCore.row j).kappa1 := by
  simp only [gamma, secondFunctionalMotherGammaSum, secondFunctionalMotherGamma,
    wuBoxPhi, convolutionSieveCount, mul_add, sum_add_distrib, mul_left_comm, mul_sum]

theorem gamma_one_upper {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      gamma j N δ 1 ≤
        (4 * wuUpperCoefficient (Wu04RemainingCore.row j).S +
          wuUpperCoefficient (Wu04RemainingCore.row j).kappa1 + ε) * theta j N δ +
          ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hphi⟩ := phi_upper hd hh (show 0 < ε/5 by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN he j
  have hg := row_analytic j
  have h1 := (row_log_domains j).1
  have hS := hphi N hN he j (Wu04RemainingCore.row j).S
    (by linarith [hg.three_le_S]) (by linarith [hg.S_le_five])
  have hB := hphi N hN he j (Wu04RemainingCore.row j).kappa1
    (by linarith) (hg.mother.kappa1_le_S.trans hg.mother.S_le_ten)
  rw [gamma_one_identity]
  linarith only [hS, hB]

#check @ap_paid
#check @ap_small
#check @phi_upper
#check @gamma_one_identity
#check @gamma_one_upper
#print axioms ap_paid
#print axioms ap_small
#print axioms phi_upper
#print axioms gamma_one_identity
#print axioms gamma_one_upper
end WuPaper.R2GammaHigh
