import W15Budget
import MixedFinalCount

namespace WuTarget.W15
open Real Wu2008DoubleSieve Filter
open scoped Topology
noncomputable section

theorem original_mother_lower :
    Wu08FourMother.Qoriginal - Phase20.rawPsi - Phase18.g18 + independentFloor/4 <
      Wu08FourMother.Qoriginal + HighConsumer.highGain/4 := by
  linarith only [independent_lower]

theorem original_mother_block_exact :
    4*(Wu08FourMother.Qoriginal + HighConsumer.highGain/4) =
      4*(Wu08FourMother.Qoriginal - Phase20.rawPsi - Phase18.g18) +
        (4*Phase20.rawPsi + 4*Phase18.g18 + HighConsumer.highGain) := by
  ring

theorem high_original_domain_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 ≤ δ → δ < d →
      highFloor-ε <
        4*∫ v : ℝ × ℝ, (MixedPayment.highRegion δ).indicator HighConsumer.highGainKernel v := by
  obtain ⟨d,hd,h⟩ := MixedRecovery.original_highGain_small_delta hε
  refine ⟨d,hd,fun δ hδ hδd => ?_⟩
  linarith only [highGain_lower, h δ hδ hδd]

theorem actual_high_increment {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ d →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ᶠ N : ℕ in atTop,
        (highFloor-ε)*truncatedSixthMassScale N ≤
          MixedEta.highMain N n δ - truncatedSixthLowerNormalizedMain N δ 0
            (MixedEta.selected N n (MixedSixth.highCells δ n)) := by
  obtain ⟨d,hd,h⟩ := HighIncrement.actual_highGain_lower hε
  refine ⟨d,hd,?_⟩
  intro δ hδ hδd
  obtain ⟨n0,hn⟩ := h δ hδ hδd
  refine ⟨n0,fun n hnn => ?_⟩
  filter_upwards [hn n hnn, eventually_ge_atTop (4 : ℕ)] with N hN hN4
  exact (mul_le_mul_of_nonneg_right (by linarith only [highGain_lower])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

theorem ordinary_P2_independent {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Wu08FourMother.Qoriginal - Phase20.rawPsi - Phase18.g18 + independentFloor/4 - ε) *
          U8CanonicalMother.M N ≤
            ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
              ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδmax,hδhi,T,hT,hcount⟩ := MixedFinal.ordinary_P2 hε hdmax
  refine ⟨δ,hδ,hδmax,hδhi,T,hT,?_⟩
  intro N hN he
  have hM := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  change 0 ≤ U8CanonicalMother.M N at hM
  exact (mul_le_mul_of_nonneg_right (by linarith only [original_mother_lower]) hM).trans
    (hcount N hN he)

theorem ordinary_P2_rounded {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Wu08FourMother.Qoriginal - Phase20.rawPsi - Phase18.g18 + 2493/4000000 - ε) *
          U8CanonicalMother.M N ≤
            ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
              ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδmax,hδhi,T,hT,hcount⟩ := ordinary_P2_independent hε hdmax
  refine ⟨δ,hδ,hδmax,hδhi,T,hT,?_⟩
  intro N hN he
  have hM := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  change 0 ≤ U8CanonicalMother.M N at hM
  exact (mul_le_mul_of_nonneg_right (by linarith only [independentFloor_rounded]) hM).trans
    (hcount N hN he)

end
end WuTarget.W15
