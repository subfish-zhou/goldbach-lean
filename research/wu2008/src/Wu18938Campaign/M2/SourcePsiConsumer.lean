import Wu18938Campaign.M2.SourceCountConsumer
import Wu18938Campaign.M2.E3Payment
import WSrcSingleCoupledHigh

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve WuSource.SrcSingle
open scoped Classical

theorem psi2_terminal_signed_mother {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    5 * psiCount (j.castAdd 4) N ≤
      ∑ p ∈ psiPrimes (j.castAdd 4) N,
        terminalSignedLocal N p
          (wuLocalCutoff N δ p (Wu04RemainingCore.row j).S)
          (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa1)
          (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa2)
          (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa3)
          (wuLocalCutoff N δ p (Wu04RemainingCore.row j).s) := by
  have h := terminal_psi_actual_count j hN hd hh
  convert h using 1 <;> fin_cases j <;>
    norm_num [psiCount, psiPrimes, psiLeft, psiRight, psiNode, sourceNode,
      terminalPsiPrimes, terminalPsiLeft, terminalPsiRight, terminalRow,
      Wu04RemainingCore.row, ActualNineFeedback.coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]
  all_goals rfl

theorem psi2_E3_signed_payment {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    (∑ p ∈ psiPrimes (j.castAdd 4) N,
      (secondFunctionalMotherPrefixTerm N p N
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa1)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa2)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa3)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).s) [3, 3, 3, 3] -
      2 * originalE3 N p
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa3)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).s))) ≤
      secondFunctionalMotherGammaSum (Wu04RemainingCore.row j) N δ
        (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N) 21 := by
  unfold secondFunctionalMotherGammaSum boxConvolutionSupport
  rw [SingleUpperCounts.single_weighted_sum]
  apply sum_le_sum
  intro p hp
  have hg := (ActualNineFeedback.coupledRow_geometry j.succ).1.mother
  change (Wu04RemainingCore.row j).MotherAdmissible at hg
  have hs : 0 < (Wu04RemainingCore.row j).s := by linarith [hg.one_le_s]
  have hratio := (seven_ratio_geometry (j.castAdd 4) hN hd hh hp).1.le
  have hae := high_cutoff_antitone hratio (hs.trans_le hg.s_le_kappa3)
    (hg.kappa3_lt_kappa2.le.trans (hg.kappa2_lt_kappa1.le.trans hg.kappa1_le_S))
  have hcut := seven_cutoff_geometry (j.castAdd 4) hN hd hh hp
  rw [(seven_source_rows.1 j).1, (seven_source_rows.1 j).2] at hcut
  have hf : wuLocalCutoff N δ p (Wu04RemainingCore.row j).s ≤ (p : ℝ) :=
    hcut.2.2.1.trans hcut.2.2.2.le
  exact gamma21_original_E3_payment hae (fun r hr =>
    (Nat.coprime_primes (mem_primeWindow.mp hr).1 (mem_primeWindow.mp hp).1).mpr
      (ne_of_lt (by exact_mod_cast (mem_primeWindow.mp hr).2.2.2.trans_le hf)))

end Wu18938Campaign.M2
