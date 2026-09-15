import SrcSingleRoot

noncomputable section
namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve Real Finset
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def theta (j : Fin 7) (N : ℕ) (δ : ℝ) : ℝ :=
  boxTheta N ((N : ℝ) ^ levelExponent δ) (fun _ : Fin 1 => psiPrimes j N)

def atom (N : ℕ) (δ : ℝ) (p : ℕ) : ℝ :=
  4 * logarithmicIntegral N * wuSingularSeries (p * N) /
    ((Nat.totient p : ℝ) * log (psiRatio N δ p))

theorem theta_sum (j : Fin 7) (N : ℕ) (δ : ℝ) :
    theta j N δ = ∑ p ∈ psiPrimes j N, atom N δ p := by
  unfold theta boxTheta atom psiRatio
  rw [mul_sum]
  simpa only [mul_div_assoc, boxConvolutionSupport, mul_left_comm] using
    SingleUpperCounts.single_weighted_sum (psiPrimes j N)
      (fun p => 4 * logarithmicIntegral N * wuSingularSeries (p * N) /
        ((Nat.totient p : ℝ) * log ((N : ℝ) ^ levelExponent δ / p)))

theorem atom_nonneg {j : Fin 7} {N p : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hp : p ∈ psiPrimes j N) :
    0 ≤ atom N δ p := by
  have hli := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0
    (by norm_num) (by exact_mod_cast hN : (2 : ℝ) ≤ N)
  have hC := wuSingularSeries_pos (p * N)
    (Nat.mul_pos (mem_primeWindow.mp hp).1.pos (by omega))
  have hl := log_pos (seven_ratio_geometry j hN hd hh hp).1
  unfold atom
  positivity

theorem theta_nonneg {j : Fin 7} {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) : 0 ≤ theta j N δ := by
  rw [theta_sum]
  exact sum_nonneg (fun _ hp => atom_nonneg hN hd hh hp)

theorem cutoff_range {j : Fin 7} {N p : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hb : a ≤ psiTop j) :
    (N : ℝ) ^ (1 / 40 : ℝ) ≤ wuLocalCutoff N δ p a ∧
      wuLocalCutoff N δ p a ≤ (N : ℝ) ^ truncatedSixthLowerAlpha ∧
      1 < wuLocalCutoff N δ p a := by
  have hg := seven_parameter_geometry j
  have hs : 0 < psiNode j := by linarith [hg.1]
  have hS : 0 < psiTop j := by linarith [hg.2.2.1]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hr := seven_ratio_geometry j hN hd hh hp
  have hcuts := seven_cutoff_geometry j hN hd hh hp
  have hlow : (N : ℝ) ^ (1 / 40 : ℝ) ≤ wuLocalCutoff N δ p (psiTop j) := by
    calc
      _ ≤ (N : ℝ) ^ ((levelExponent δ - psiRight j) * (1 / psiTop j)) := by
        apply rpow_le_rpow_of_exponent_le hN1
        have hbase := hg.2.2.2.2.2.2.2.2.2.2
        have hdelta := div_le_div_of_nonneg_right
          (show 1 / 2 - 1 / 100 - psiRight j ≤ levelExponent δ - psiRight j by
            unfold levelExponent; linarith) hS.le
        simpa only [div_eq_mul_inv, one_mul] using hbase.trans hdelta
      _ = ((N : ℝ) ^ (levelExponent δ - psiRight j)) ^ (1 / psiTop j) :=
        rpow_mul (Nat.cast_nonneg N) _ _
      _ ≤ _ := rpow_le_rpow (by positivity) hr.2.2 (one_div_nonneg.mpr hS.le)
  have hdown := high_cutoff_antitone hr.1.le (hs.trans_le ha) hb
  have hup := high_cutoff_antitone hr.1.le hs ha
  exact ⟨hlow.trans hdown, hup.trans hcuts.2.2.1, hcuts.1.trans_le hdown⟩

theorem outer_le_N {j : Fin 7} {N p : ℕ}
    (hN : 2 ≤ N) (hp : p ∈ psiPrimes j N) : p ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hr := (seven_parameter_geometry j).2.2.2.2.2.2.2.2.2.1
  have h := (mem_primeWindow.mp hp).2.2.2.le.trans
    (rpow_le_rpow_of_exponent_le hN1 (hr.trans (by norm_num : (1 / 3 : ℝ) ≤ 1)))
  rw [rpow_one] at h
  exact_mod_cast h

theorem single_modulus_envelope {j : Fin 7} {N p : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hb : a ≤ psiTop j) :
    ((p * N : ℕ) : ℝ) ≤ (wuLocalCutoff N δ p a) ^ (80 : ℝ) := by
  calc
    _ ≤ (N : ℝ) ^ (2 : ℝ) := by
      norm_cast
      nlinarith [Nat.mul_le_mul_right N (outer_le_N hN hp)]
    _ = ((N : ℝ) ^ (1 / 40 : ℝ)) ^ (80 : ℝ) := by
      rw [← rpow_mul (Nat.cast_nonneg N)]; norm_num
    _ ≤ _ := rpow_le_rpow (by positivity) (cutoff_range hN hd hh hp ha hb).1 (by norm_num)

theorem single_level_geometry {j : Fin 7} {N p : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) :
    1 < wuVariableRosserLevel N δ p ∧
      wuLocalCutoff N δ p a ≤ (wuVariableRosserLevel N δ p : ℝ) := by
  have hr := (seven_ratio_geometry j hN hd hh hp).1
  have hapos : 0 < a := by linarith [(seven_parameter_geometry j).1]
  have hz : wuLocalCutoff N δ p a ≤ psiRatio N δ p := by
    calc
      _ ≤ (psiRatio N δ p) ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hr.le
          ((div_le_iff₀ hapos).mpr (by linarith [(seven_parameter_geometry j).1]))
      _ = _ := rpow_one _
  have hf : psiRatio N δ p < (wuVariableRosserLevel N δ p : ℝ) := by
    unfold psiRatio wuVariableRosserLevel levelExponent
    exact_mod_cast Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 2 - δ) / p)
  exact ⟨by exact_mod_cast hr.trans hf, hz.trans hf.le⟩

theorem actual_phi_ge_two {j : Fin 7} {N p : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) : 2 ≤ omega3XPhi N p δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hlN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hlp : 0 ≤ log (p : ℝ) :=
    log_nonneg (by exact_mod_cast (mem_primeWindow.mp hp).1.one_lt.le)
  have hlR := log_pos (seven_ratio_geometry j hN hd hh hp).1
  unfold omega3XPhi
  apply (le_div_iff₀ hlR).mpr
  unfold psiRatio levelExponent
  rw [log_div hN0.ne' hp0.ne', log_div (rpow_pos_of_pos hN0 _).ne' hp0.ne',
    log_rpow hN0]
  nlinarith only [mul_nonneg hd.le hlN.le, hlp]

theorem coupled_actual_kernel_scalar {j : Fin 7} {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (row : SecondFunctionalParameters) (hp : row.MotherAdmissible) (hs : 2 ≤ row.s) :
    (∑ p ∈ psiPrimes j N, atom N δ p *
      ((∑ k : Fin 6, LowerTripleSourceK.sourceIntegralK N p δ row k) +
        secondFunctionalCombinedKernel N p δ row)) ≤
      SecondFunctionalCoupled.jointSup row * theta j N δ := by
  simp_rw [← SecondFunctionalCoupled.kernel_actual]
  rw [theta_sum, mul_sum]
  apply sum_le_sum
  intro p hpwin
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (SecondFunctionalCoupled.kernel_le_jointSup row hp hs (actual_phi_ge_two hN hd hh hpwin))
    (atom_nonneg hN hd hh hpwin)

#check @cutoff_range
#check @coupled_actual_kernel_scalar
#print axioms coupled_actual_kernel_scalar
end WuSource.SrcSingle.Analytic
