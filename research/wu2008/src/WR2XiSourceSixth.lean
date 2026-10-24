import W01ContinuousCount
import WR2XiCandidateCount

noncomputable section
namespace WuTarget.W01Continuous
open Wu2008DoubleSieve NodeExtension Filter
open scoped Topology

theorem actual_sixth {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d →
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin+continuousGain x+HighConsumer.highGain-ε)*
            U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨η,hη,hη1,a,ha,ha0,ha1,hm⟩ := continuous_mixed_normalization hn hd0 hx (half_pos hε)
  refine ⟨min a (50*HighBoxRecovery.highEta),
    lt_min ha (by norm_num [HighBoxRecovery.highEta]),
    (min_le_left _ _).trans ha0,(min_le_left _ _).trans ha1,?_⟩
  intro δ hδ hδd
  have hda := hδd.trans_le (min_le_left _ _)
  have hdhi := hδd.le.trans (min_le_right _ _)
  obtain ⟨n,hn⟩ := (hm δ hδ hda).exists
  obtain ⟨Tm,hTm⟩ := eventually_atTop.mp hn
  obtain ⟨Tc,hTc,hc⟩ := MixedSixth.actual_count hδ hdhi (hda.trans_le ha1)
    hη hη1 (half_pos hε) n
  refine ⟨max Tm Tc,hTc.trans (le_max_right _ _),?_⟩
  intro N hN he
  have hmN := hTm N ((le_max_left _ _).trans hN)
  have hcN := hc N ((le_max_right _ _).trans hN) he
  change (truncatedSixthLowerF6lin+continuousGain x+HighConsumer.highGain-ε/2)*
    U8CanonicalMother.M N ≤ MixedSixth.main N n δ η at hmN
  linarith only [hmN,hcN]

end WuTarget.W01Continuous

namespace WuPaper.R2Xi.SourceSixth
open Wu2008DoubleSieve

def amount : ℝ := WuTarget.W01Continuous.continuousGain CandidateCount.nodes+HighConsumer.highGain

theorem supplied_sixth : SixthSlotAssembly.SixthLower amount := by
  intro ε hε
  obtain ⟨d0,hd0,_,hx⟩ := CandidateCount.nodes_actual
  obtain ⟨d,hd,_,_,hc⟩ := WuTarget.W01Continuous.actual_sixth
    CandidateCount.nodes_nonneg hd0 hx hε
  obtain ⟨T,hT,hcount⟩ := hc (d/2) (half_pos hd) (half_lt_self hd)
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  simpa only [amount, U8CanonicalMother.M, mul_assoc, mul_div_assoc, add_assoc] using hcount N hN hEven

end WuPaper.R2Xi.SourceSixth
#print axioms WuPaper.R2Xi.SourceSixth.supplied_sixth
