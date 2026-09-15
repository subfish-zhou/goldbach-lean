import SrcSingleAnalyticGeometry

noncomputable section
namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve Real Finset Filter LiLiuPrereqBuchstab
open scoped Classical Topology BigOperators
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem outer_log_bound {j : Fin 7} {N p : ℕ}
    (hN : 2 ≤ N) (hp : p ∈ psiPrimes j N) : log (p : ℝ) / log N ≤ psiRight j := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  apply (div_le_iff₀ hl).mpr
  rw [← log_rpow hN0]
  exact log_le_log (by exact_mod_cast (mem_primeWindow.mp hp).1.pos)
    (mem_primeWindow.mp hp).2.2.2.le

theorem theta_total_mass {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 7,
      0 ≤ theta j N δ ∧ theta j N δ ≤ 560 * truncatedSixthMassScale N := by
  obtain ⟨T1, hT14, hT1⟩ := SingleUpperPrimePayment.reciprocal_mass_bound
  obtain ⟨T2, _, hT2⟩ := SingleUpperPrimePayment.denominator_payment
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T3, _, hT3⟩ := SingleUpperPrimePayment.trueLi_upper
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), fun N hN j => ?_⟩
  have hN4 : 4 ≤ N := hT14.trans (by omega)
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN2)
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN2)
  have hg := seven_parameter_geometry j
  have hleft : (1 / 15 : ℝ) ≤ psiLeft j :=
    (by norm_num : (1 / 15 : ℝ) ≤ 1 / 4).trans hg.2.2.2.2.2.2.2.1.le
  have hright : psiRight j ≤ (1 / 3 : ℝ) := hg.2.2.2.2.2.2.2.2.2.1
  have hden (p : ℕ) (hp : p ∈ psiPrimes j N) :
      2 < p ∧ 1 / ((p : ℝ) - 2) ≤ 2 / p := by
    have h := hT2 N (by omega) p (mem_primeWindow.mp hp).1
      ((rpow_le_rpow_of_exponent_le hNr hleft).trans (mem_primeWindow.mp hp).2.2.1)
    exact ⟨h.1, by norm_num at h ⊢; exact h.2.1⟩
  have hsum : (∑ p ∈ psiPrimes j N, 1 / ((p : ℝ) - 2)) ≤ 10 := by
    calc
      _ ≤ ∑ p ∈ psiPrimes j N, 2 / (p : ℝ) := sum_le_sum (fun p hp => (hden p hp).2)
      _ = 2 * ∑ p ∈ psiPrimes j N, 1 / (p : ℝ) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ 2 * ∑ p ∈ primesIcc ((N : ℝ) ^ psiLeft j) ((N : ℝ) ^ psiRight j), 1 / (p : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeWindow.mp hp
          exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr ⟨hpp, hlo, hhi.le⟩
        · intros; positivity
      _ ≤ 10 := by
        have h := hT1 N (by omega) (psiLeft j) (psiRight j)
          hleft hg.2.2.2.2.2.2.2.2.1.le hright
        linarith
  have hc (p : ℕ) (hp : p ∈ psiPrimes j N) :
      (1 / 7 : ℝ) ≤ (1 / 2 - δ) - log (p : ℝ) / log N := by
    linarith [(outer_log_bound hN2 hp).trans hright]
  have hweighted : (∑ p ∈ psiPrimes j N,
      1 / (((p : ℝ) - 2) * ((1 / 2 - δ) - log (p : ℝ) / log N))) ≤ 70 := by
    calc
      _ ≤ ∑ p ∈ psiPrimes j N, 7 * (1 / ((p : ℝ) - 2)) := by
        apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) < p := by exact_mod_cast (hden p hp).1
        have hcp : 0 < (1 / 2 - δ) - log (p : ℝ) / log N := by linarith [hc p hp]
        have hi : 1 / ((1 / 2 - δ) - log (p : ℝ) / log N) ≤ 7 :=
          (div_le_iff₀ hcp).mpr (by linarith [hc p hp])
        calc
          _ = (1 / ((p : ℝ) - 2)) * (1 / ((1 / 2 - δ) - log (p : ℝ) / log N)) := by
            simp only [one_div, mul_inv_rev]; ring
          _ ≤ (1 / ((p : ℝ) - 2)) * 7 := mul_le_mul_of_nonneg_left hi (by positivity)
          _ = _ := by ring
      _ = 7 * ∑ p ∈ psiPrimes j N, 1 / ((p : ℝ) - 2) := (mul_sum ..).symm
      _ ≤ 70 := by linarith
  have hcoef : 4 * logarithmicIntegral N * wuSingularSeries N / log N ≤
      8 * truncatedSixthMassScale N := by
    calc
      _ ≤ 4 * ((1 + 1) * (N : ℝ) / log N) * wuSingularSeries N / log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT3 N (by omega))
            (by norm_num)) hC) hlog.le
      _ = _ := by unfold truncatedSixthMassScale; ring
  refine ⟨theta_nonneg hN2 hd hh, ?_⟩
  rw [theta, levelExponent, SingleUpperNormalization.theta_single_exact hN2 (psiPrimes j N)
    (fun p hp => ⟨(mem_primeWindow.mp hp).1, (hden p hp).1, (mem_primeWindow.mp hp).2.1⟩)]
  calc
    _ ≤ (4 * logarithmicIntegral N * wuSingularSeries N / log N) * 70 :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ (8 * truncatedSixthMassScale N) * 70 := mul_le_mul_of_nonneg_right hcoef (by norm_num)
    _ = _ := by ring

theorem logarithmic_error_payment {C ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      C * N / log (N : ℝ) ^ (3 : ℝ) ≤ ε * truncatedSixthMassScale N := by
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (C / (ε * wuSingularSeries 1))))
  refine ⟨max 4 T, le_max_left _ _, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ))
    (by omega : 0 < N) (one_dvd N)
  have hbudget : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hT N (by omega))
    have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hseries heps.le) hlog.le
    nlinarith
  calc
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (2 : ℕ)) := by norm_num; ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ) / log (N : ℝ) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

theorem single_remainder_paid {δ ε : ℝ} (hd : 0 < δ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 7,
      ∀ (upper : Bool) (cut : ℕ → ℝ),
      |∑ p ∈ psiPrimes j N,
        ordinaryRosserRemainder upper N p (wuVariableRosserLevel N δ p) (cut p)| ≤
          ε * truncatedSixthMassScale N := by
  obtain ⟨C, _, T, hBV⟩ := SingleUpperCounts.global_signed_bv
    (show (0 : ℝ) < 1 / 4 by norm_num) hd (show (0 : ℝ) < 3 by norm_num)
  obtain ⟨M, hM4, hM⟩ := logarithmic_error_payment (C := C) heps
  refine ⟨max M T, hM4.trans (le_max_left _ _), fun N hN j upper cut => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  apply (hBV N (by omega) (psiPrimes j N) (fun p hp =>
    ⟨(mem_primeWindow.mp hp).1, (mem_primeWindow.mp hp).2.1,
      (rpow_le_rpow_of_exponent_le hNr
        (seven_parameter_geometry j).2.2.2.2.2.2.2.1.le).trans (mem_primeWindow.mp hp).2.2.1⟩)
    upper (wuVariableRosserLevel N δ) cut
    (fun p _ => (wuVariableRosserLevel_eq_combined N p δ).le)).trans
  exact hM N (by omega)

theorem normalized_point_upper {δ η : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heta : 0 < η) (heta1 : η ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (j : Fin 7) (p : ℕ), p ∈ psiPrimes j N → ∀ a : ℝ,
      psiNode j ≤ a → a ≤ psiTop j →
      ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p) (wuLocalCutoff N δ p a) ≤
        (wuUpperCoefficient a + 15 * η) * (4 * wuSingularSeries (p * N) / log (psiRatio N δ p)) := by
  have hrho : 0 < exp eulerMascheroniConstant * η / 2 := by positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_upper_density_canonical_bounded_local hrho
  obtain ⟨Z1, hZ1⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative 80 η (by norm_num) heta)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_ge_atTop (max 2 (max Z Z1))))
  refine ⟨max 4 T, le_max_left _ _, fun N hN he j p hp a ha hb => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hz := (hT N (by omega)).trans (cutoff_range hN2 hd hh hp ha hb).1
  have hz2 := (le_max_left _ _).trans hz
  have hzZ := (le_max_left Z Z1).trans ((le_max_right _ _).trans hz)
  have hzZ1 := (le_max_right Z Z1).trans ((le_max_right _ _).trans hz)
  have hr := (seven_ratio_geometry j hN2 hd hh hp).1
  have hR0 : 0 < psiRatio N δ p := zero_lt_one.trans hr
  have hlR : 0 < log (psiRatio N δ p) := log_pos hr
  have hapos : 0 < a := by linarith [(seven_parameter_geometry j).1]
  have ha1 : 1 ≤ a := by linarith [(seven_parameter_geometry j).1]
  have ha10 : a ≤ 10 := hb.trans ((seven_parameter_geometry j).2.2.2.1.trans (by norm_num))
  have hlz : log (wuLocalCutoff N δ p a) = (1 / a) * log (psiRatio N δ p) := log_rpow hR0 _
  have hsarg : a = log (psiRatio N δ p) / log (wuLocalCutoff N δ p a) := by
    rw [hlz]; field_simp
  have hM0 : 0 < p * N := Nat.mul_pos (mem_primeWindow.mp hp).1.pos (by omega)
  have hlocal := hZ1 (wuLocalCutoff N δ p a) hzZ1 (p * N) hM0 (he.mul_left p)
    (single_modulus_envelope hN2 hd hh hp ha hb)
  have hnormal : 2 * a * wuSingularSeries (p * N) /
      (exp eulerMascheroniConstant * log (psiRatio N δ p)) =
      2 * exp (-eulerMascheroniConstant) * wuSingularSeries (p * N) /
        log (wuLocalCutoff N δ p a) := by
    rw [hlz, exp_neg]; field_simp
  rw [← hnormal] at hlocal
  have hn0 : 0 < 2 * a * wuSingularSeries (p * N) /
      (exp eulerMascheroniConstant * log (psiRatio N δ p)) := by
    have := wuSingularSeries_pos _ hM0
    positivity
  have hprod : localSieveProduct (p * N) (wuLocalCutoff N δ p a) ≤
      (1 + η) * (2 * a * wuSingularSeries (p * N) /
        (exp eulerMascheroniConstant * log (psiRatio N δ p))) := by
    apply (div_le_iff₀ hn0).mp
    linarith [(le_abs_self (_ : ℝ)).trans hlocal]
  have hF : 0 ≤ jr1965F a + exp eulerMascheroniConstant * η / 2 :=
    add_nonneg (jr1965F_pos hapos).le hrho.le
  have hmain := hdensity N p he (wuLocalCutoff N δ p a) (psiRatio N δ p) a
    hzZ hz2 hR0 hsarg (by linarith [(seven_parameter_geometry j).1]) ha10
  exact hmain.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
    (canonical_upper_bounded_normalization_budget ha1 ha10 (wuSingularSeries_pos _ hM0).le
      hlR heta.le heta1))

theorem phi_single (j : Fin 7) (N : ℕ) (δ a : ℝ) :
    wuBoxPhi N δ (fun _ : Fin 1 => psiPrimes j N) a =
      ∑ p ∈ psiPrimes j N, (sourceSieveCount N p (p * N) (wuLocalCutoff N δ p a) : ℝ) := by
  unfold wuBoxPhi convolutionSieveCount
  exact SingleUpperCounts.single_weighted_sum _ _

theorem phi_upper_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ (j : Fin 7) (a : ℝ),
      psiNode j ≤ a → a ≤ psiTop j →
      wuBoxPhi N δ (fun _ : Fin 1 => psiPrimes j N) a ≤
        wuUpperCoefficient a * theta j N δ + ε * truncatedSixthMassScale N := by
  let η := min 1 (ε / 16800)
  have heta : 0 < η := lt_min (by norm_num) (by positivity)
  have heta1 : η ≤ 1 := min_le_left _ _
  have hetaFee : 8400 * η ≤ ε / 2 := by
    have h := min_le_right (1 : ℝ) (ε / 16800)
    dsimp [η]; linarith
  obtain ⟨T1, hT14, hT1⟩ := normalized_point_upper hd hh heta heta1
  obtain ⟨T2, _, hT2⟩ := single_remainder_paid hd (half_pos heps)
  obtain ⟨T3, _, hT3⟩ := theta_total_mass hd hh
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), fun N hN he j a ha hb => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN2)
  have hf :
      wuBoxPhi N δ (fun _ : Fin 1 => psiPrimes j N) a ≤
        (wuUpperCoefficient a + 15 * η) * theta j N δ +
          ∑ p ∈ psiPrimes j N,
            ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p) (wuLocalCutoff N δ p a) := by
    rw [phi_single, theta_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hgeom := single_level_geometry hN2 hd hh hp ha
    have hfinite := ordinaryRosser_upper_finite (N := N) (d := p) hgeom.1 hgeom.2
    have hmain := mul_le_mul_of_nonneg_left (hT1 N (by omega) he j p hp a ha hb)
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient p)))
    have heq : logarithmicIntegral N / (Nat.totient p : ℝ) *
        ((wuUpperCoefficient a + 15 * η) * (4 * wuSingularSeries (p * N) / log (psiRatio N δ p))) =
          (wuUpperCoefficient a + 15 * η) * atom N δ p := by unfold atom; ring
    rw [heq] at hmain
    exact hfinite.trans (add_le_add hmain le_rfl)
  have hr := (le_abs_self (_ : ℝ)).trans
    (hT2 N (by omega) j true (fun p => wuLocalCutoff N δ p a))
  have hscale := truncatedSixthClosure_scale_nonneg (hT14.trans (by omega : T1 ≤ N))
  have hfee : 15 * η * theta j N δ ≤ (ε / 2) * truncatedSixthMassScale N := by
    calc
      _ ≤ 15 * η * (560 * truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left (hT3 N (by omega) j).2 (by positivity)
      _ = (8400 * η) * truncatedSixthMassScale N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hetaFee hscale
  nlinarith only [hf, hr, hfee]

#check @phi_upper_paid
#print axioms phi_upper_paid
#print axioms theta_total_mass
end WuSource.SrcSingle.Analytic
