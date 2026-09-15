import WSrcSingleCoupledHigh
import HighO2TerminalFinal
import HighFullActual

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighTheta HighBoxRecovery Real Finset
open scoped Classical

def windows (j : Fin 3) (N : ℕ) : Fin 1 → Finset ℕ :=
  fun _ => psiPrimes (j.castAdd 4) N

def theta (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (windows j N)

def gamma (j : Fin 3) (N : ℕ) (δ : ℝ) (i : ℕ) : ℝ :=
  secondFunctionalMotherGammaSum (Wu04RemainingCore.row j) N δ (windows j N) i

theorem support_eq (j : Fin 3) (N : ℕ) :
    boxConvolutionSupport (windows j N) = psiPrimes (j.castAdd 4) N :=
  SingleUpperCounts.single_support _

theorem prime_geometry {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hm : d ∈ psiPrimes (j.castAdd 4) N) :
    d.Prime ∧ d.Coprime N ∧ (N : ℝ)^highEta ≤ d ∧
      0 < d ∧ d ≤ N ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-100*highEta) ∧
      (N : ℝ)^(10*highEta) ≤ (N : ℝ)^(1/2-δ)/d ∧
      1 < (N : ℝ)^(1/2-δ)/d := by
  have hp := mem_primeWindow.mp hm
  have hg := seven_parameter_geometry (j.castAdd 4)
  have hleft : (1/4 : ℝ) < psiLeft (j.castAdd 4) := hg.2.2.2.2.2.2.2.1
  have hright : psiRight (j.castAdd 4) ≤ (1/3 : ℝ) := hg.2.2.2.2.2.2.2.2.2.1
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hratio := seven_ratio_geometry (j.castAdd 4) hN hd hh hm
  refine ⟨hp.1, hp.2.1, ?_, hp.1.pos, ?_, ?_, ?_, hratio.1⟩
  · exact (rpow_le_rpow_of_exponent_le hN1.le
      (by norm_num [highEta] at *; linarith : highEta ≤ psiLeft (j.castAdd 4))).trans
        hp.2.2.1
  · have h := hp.2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le hN1.le (hright.trans (by norm_num : (1/3 : ℝ) ≤ 1)))
    rw [rpow_one] at h
    exact_mod_cast h
  · exact hp.2.2.2.le.trans (rpow_le_rpow_of_exponent_le hN1.le
      (hright.trans (by norm_num [highEta] : (1/3 : ℝ) ≤ 1/2-100*highEta)))
  · exact (rpow_le_rpow_of_exponent_le hN1.le
      (by dsimp [levelExponent]; norm_num [highEta] at *; linarith :
        10*highEta ≤ levelExponent δ - psiRight (j.castAdd 4))).trans hratio.2.2

theorem support_size {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    ∀ d ∈ boxConvolutionSupport (windows j N),
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
  intro d hm
  rw [support_eq] at hm
  have h := (prime_geometry j hN hd hh hm).2.2.2.2.2.1
  exact h.trans (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega))
    (by norm_num [highEta] at *; linarith))

theorem theta_nonneg {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    0 ≤ theta j N δ := by
  have hli : 0 ≤ AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans (box_trueLi_lower hN)
  unfold theta boxTheta
  apply mul_nonneg (mul_nonneg (by norm_num) hli)
  apply sum_nonneg
  intro d hm
  rw [support_eq] at hm
  have hg := prime_geometry j (by omega) hd hh hm
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos hg.2.2.2.1 (by omega))).le
  · exact mul_nonneg (Nat.cast_nonneg _) (log_pos hg.2.2.2.2.2.2.2).le

theorem row_analytic (j : Fin 3) :
    MotherPair.AnalyticParameters (Wu04RemainingCore.row j) :=
  (ActualNineFeedback.coupledRow_geometry j.succ).1

theorem row_log_domains (j : Fin 3) :
    3 ≤ (Wu04RemainingCore.row j).kappa1 ∧
      2 ≤ (Wu04RemainingCore.row j).S - (Wu04RemainingCore.row j).S /
        (Wu04RemainingCore.row j).s ∧
      2 ≤ (Wu04RemainingCore.row j).S - (Wu04RemainingCore.row j).S /
        (Wu04RemainingCore.row j).kappa2 ∧
      2 ≤ (Wu04RemainingCore.row j).S - (Wu04RemainingCore.row j).S /
        (Wu04RemainingCore.row j).kappa3 :=
  SecondFunctionalSignedCore.original_log_domains j.succ

#check @windows
#check @theta
#check @gamma
#check @support_eq
#check @prime_geometry
#check @support_size
#check @theta_nonneg
#check @row_analytic
#check @row_log_domains
#print axioms windows
#print axioms theta
#print axioms gamma
#print axioms support_eq
#print axioms prime_geometry
#print axioms support_size
#print axioms theta_nonneg
#print axioms row_analytic
#print axioms row_log_domains
end WuPaper.R2GammaHigh
