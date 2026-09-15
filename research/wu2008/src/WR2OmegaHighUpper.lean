import WR2OmegaHighCarrier

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighBoxRecovery
open Finset Real Filter
open scoped Classical Topology Interval BigOperators

theorem actual_AP_paid {δ ε : ℝ} (hd : 0 < δ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 4,
      convolutionAPError N (convolutionModulusCutoff N δ) (windows j N) ≤
        ε * truncatedSixthMassScale N ∧
      convolutionAPError N (convolutionModulusCutoff N δ)
        (Fin.cons (HighO2Terminal.apPrimeCover N) (windows j N)) ≤
          ε * truncatedSixthMassScale N := by
  obtain ⟨C, hC, T0, hb⟩ := convolution_bombieri_vinogradov 2
    (show 0 < highEta by norm_num [highEta]) hd (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T1, hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * wuSingularSeries 1))))
  refine ⟨max 4 (max T0 T1), le_max_left _ _, ?_⟩
  intro N hN j
  have hN2 : 2 ≤ N := by omega
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN2)
  have hs : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hc : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hlogBudget N (by omega))
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs heps.le) hl.le
    dsimp only [Function.comp_apply] at h
    nlinarith
  have hpay : C * N / log (N : ℝ) ^ (3 : ℝ) ≤ ε * truncatedSixthMassScale N := by
    calc
      _ = (C / log N) * ((N : ℝ) / log N ^ 2) := by norm_num; ring
      _ ≤ (ε * wuSingularSeries N) * ((N : ℝ) / log N ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by unfold truncatedSixthMassScale; ring
  have hw : ∀ k p, p ∈ windows j N k →
      p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ highEta ≤ p :=
    fun _ p hp => ⟨(prime_geometry j hN2 hp).1, (prime_geometry j hN2 hp).2.1,
      (prime_geometry j hN2 hp).2.2.1⟩
  refine ⟨(hb N (by omega) 1 (by norm_num) _ hw).trans hpay, ?_⟩
  apply (hb N (by omega) 2 le_rfl _ ?_).trans hpay
  intro k
  refine Fin.cases ?_ (fun k => hw k) k
  intro p hp
  have hm := mem_primeWindow.mp hp
  exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

theorem omega1_upper {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      (∑ p ∈ psiPrimes (index j) N, wuOmega1 N p δ (psiTop (index j))) ≤
        2 * wuUpperCoefficient (psiTop (index j)) * theta j N δ +
          ε * truncatedSixthMassScale N := by
  obtain ⟨T0, _, hm⟩ := HighFull.main_upper hd.le
    (show 0 < highEta by norm_num [highEta]) (show 0 < ε / 1920 by positivity)
  obtain ⟨T1, hT14, ha⟩ := actual_AP_paid hd (show 0 < ε / 4 by positivity)
  obtain ⟨T2, _, ht⟩ := theta_total_mass hd hh
  refine ⟨max T1 (max T0 T2), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have hN4 : 4 ≤ N := hT14.trans (by omega)
  have hg := support_geometry (N := N) j (by omega) hh
  have hpar := geometry j
  have hmain := hm N (by omega) he 1 (windows j N)
    (fun k p hp => (hg.1 k p hp).1) hg.2 (psiTop (index j))
    (by linarith [hpar.2.2.1]) (by linarith [hpar.2.2.2.1])
  have hap := (ha N (by omega) j).1
  have hr : HighCross.rosserUpper N δ (psiTop (index j)) (windows j N) ≤
      (wuUpperCoefficient (psiTop (index j)) + ε / 1920) * theta j N δ +
        (ε / 4) * truncatedSixthMassScale N := add_le_add hmain hap
  have hadm := HighCross.support_admission (windows j N) (show 2 ≤ N by omega)
    (show 0 < highEta by norm_num [highEta]) (fun k p hp => (hg.1 k p hp).1) hg.2
  have hphi := (HighCross.rosser_upper (windows j N) hadm.2
    (by linarith [hpar.2.2.1] : 1 ≤ psiTop (index j))).trans hr
  have homega : (∑ p ∈ psiPrimes (index j) N, wuOmega1 N p δ (psiTop (index j))) =
      2 * wuBoxPhi N δ (windows j N) (psiTop (index j)) := by
    rw [← wuOmega1Sum_eq_twice_Phi]
    exact (weighted_sum j N _).symm
  have hmass := (ht N (by omega) he j).2
  have hfee := mul_le_mul_of_nonneg_left hmass (show 0 ≤ ε / 960 by positivity)
  rw [homega]
  nlinarith only [hphi, hfee]

#check @WuPaper.R2OmegaHigh.actual_AP_paid
#check @WuPaper.R2OmegaHigh.omega1_upper
#print axioms WuPaper.R2OmegaHigh.actual_AP_paid
#print axioms WuPaper.R2OmegaHigh.omega1_upper
end WuPaper.R2OmegaHigh
