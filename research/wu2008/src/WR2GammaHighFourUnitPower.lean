import WR2GammaHighFourIntegralCount
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
namespace WuPaper.R2GammaHigh.FourUnit
open Wu2008DoubleSieve FourPrimeUnit Real Finset
open scoped Classical

theorem source_mass {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    actualSource N δ (Wu04RemainingCore.row j) (windows j N) k ≤
      ((N:ℝ)^(1/2-δ))^(4/(Wu04RemainingCore.row j).s) *
        boxConvolutionReciprocalMass (windows j N) := by
  have hpos : ∀ d ∈ boxConvolutionSupport (windows j N), 0 < d :=
    fun _ hm => boxConvolutionSupport_pos (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hm
  apply (source_le_envelope hpos k).trans
  change actualEnvelope N δ (Wu04RemainingCore.row j) (windows j N) k ≤ _
  rw [actual_envelope_eq]
  have hp := row_analytic j
  apply secondFunctionalUnit_mass_le _ _ _ (rpow_nonneg (Nat.cast_nonneg N) _)
    hp.two_lt_s hp.s_le_three hpos
    (fun _ hx _ => actual_profiles_geometry hx)
  intro x hx _ q hq
  have hm := (actual_profiles_geometry hx).1
  have hc := (high_cutoffs j hN hd hh hm).2.2.2
  exact fibre_geometry hc hq

/-- Single-window convolution preserves the literal harmonic majorant. -/
theorem reciprocal_mass_bound {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    boxConvolutionReciprocalMass (windows j N) ≤ 1+log (N:ℝ) := by
  have he := GammaNine.weighted_sum j N (fun d => 1/(d:ℝ))
  have hm : boxConvolutionReciprocalMass (windows j N) =
      ∑ d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N, 1/(d:ℝ) := by
    simpa only [boxConvolutionReciprocalMass, mul_one_div] using he
  rw [hm]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, 1/(d:ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd'
        have hg := prime_geometry j hN hd hh hd'
        exact mem_Icc.mpr ⟨hg.1.pos,hg.2.2.2.2.1⟩
      · intro _ _ _
        positivity
    _ = harmonic N := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := harmonic_le_one_add_log N

/-- The smallest original s is 2.3, giving a uniform exponent strictly below one. -/
theorem source_power_bound {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    actualSource N δ (Wu04RemainingCore.row j) (windows j N) k ≤
      (N:ℝ)^(20/23:ℝ)*(1+log N) := by
  have hs : (23/10:ℝ) ≤ (Wu04RemainingCore.row j).s := by
    revert j
    simp only [Wu04RemainingCore.row, ActualNineFeedback.coupledRow,
      SecondFunctionalPositive.parameters, Fin.forall_fin_succ, Fin.forall_fin_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, and_true]
    norm_num [SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]
  have hspos : 0 < (Wu04RemainingCore.row j).s := by linarith
  have hexp : (1/2-δ)*(4/(Wu04RemainingCore.row j).s) ≤ 20/23 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hs,hd]
  have hpower : ((N:ℝ)^(1/2-δ))^(4/(Wu04RemainingCore.row j).s) ≤ (N:ℝ)^(20/23:ℝ) := by
    rw [← rpow_mul (Nat.cast_nonneg N)]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hexp
  exact (source_mass j k hN hd hh).trans
    (mul_le_mul hpower (reciprocal_mass_bound j hN hd hh)
      (sum_nonneg (fun _ _ => by positivity)) (rpow_nonneg (Nat.cast_nonneg _) _))

end WuPaper.R2GammaHigh.FourUnit
#print axioms WuPaper.R2GammaHigh.FourUnit.source_power_bound
