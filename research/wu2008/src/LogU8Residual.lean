import FullLogMother
import U8MotherSmallResidual

noncomputable section
open Finset Real
open Wu2008DoubleSieve Wu2008DoubleSieve.SeventhEighth
open Wu2008DoubleSieve.TruncatedElevenClassicalCountLower
open U8MotherInsertion
namespace LogU8Residual
theorem mother_with_literal_split {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ + 16*J7 + 8*J8 +
        8*FourRoughClosedMass.I10 + 8*FourRoughClosedMass.I11 - ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) -
        2*((physicalT7 N).card : ℝ) - ((small N).card : ℝ) - ((large N).card : ℝ) -
        ((TruncatedFourPhysical.Physical10 N).card : ℝ) -
        ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤
          (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T,hT,h⟩ := FullLogMother.truncated_fixed_all_physical_lower hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hm := h N hN he
  rw [physicalT8_card_split, Nat.cast_add] at hm
  convert hm using 1
  unfold FullLogMother.psiCoefficient
  ring

/-- All other negative carriers are paid using their actual upper producers. -/
theorem fixed_small_debit {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ+8*oldSmallIntegral-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) - ((small N).card : ℝ) ≤
          (truncatedSixthFixedExpression N : ℝ) := by
  have heps : 0 < ε/5 := by positivity
  obtain ⟨Ta,hTa,ha⟩ := mother_with_literal_split hδ hδhi heps
  obtain ⟨T7,_,h7⟩ := seventh_eighth_physical_classical_upper heps
  obtain ⟨Th,_,hh⟩ := large_integral_upper heps
  obtain ⟨Tf,_,hf⟩ := FourClassical.physical10_physical11_sum_classical_upper heps
  refine ⟨max Ta (max T7 (max Th Tf)),hTa.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hNa := (le_max_left Ta (max T7 (max Th Tf))).trans hN
  have hN7hf := (le_max_right Ta (max T7 (max Th Tf))).trans hN
  have hN7 := (le_max_left T7 (max Th Tf)).trans hN7hf
  have hNhf := (le_max_right T7 (max Th Tf)).trans hN7hf
  have hNh := (le_max_left Th Tf).trans hNhf
  have hNf := (le_max_right Th Tf).trans hNhf
  have ham := ha N hNa he
  have h7m := (h7 N hN7 he).1
  have hhm := hh N hNh he
  have hfm := hf N hNf he
  rw [J8_split] at ham
  ring_nf at ham h7m hhm hfm ⊢
  linarith only [ham,h7m,hhm,hfm]

/-- The original seven-error finite mother is consumed, with its overlap two.
The remaining small debit has coefficient one, and the RHS is four times ordinary P2. -/
theorem ordinary_small_debit {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ+8*oldSmallIntegral-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) - ((small N).card : ℝ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T1,hT1,hmain⟩ := fixed_small_debit hδ hδhi (half_pos hε)
  obtain ⟨T2,_,herror⟩ := exceptional_power_error_paid (half_pos hε)
  obtain ⟨T3,_,hcutoff⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max T1 (max T2 T3),hT1.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN1 := (le_max_left T1 (max T2 T3)).trans hN
  have hN23 := (le_max_right T1 (max T2 T3)).trans hN
  have hN2 := (le_max_left T2 T3).trans hN23
  have hN3 := (le_max_right T2 T3).trans hN23
  have hm := hmain N hN1 he
  have hp := herror N hN2
  have hf := truncatedSixth_fixed_le_count (by have := hT1.trans hN1; omega) he (hcutoff N hN3)
  ring_nf at hm hp ⊢
  linarith only [hm,hp,hf]
end LogU8Residual
