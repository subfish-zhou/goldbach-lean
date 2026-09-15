import SrcSixthGainQualification
import SrcSixthGainSource
import W03Table
import W01WeightedCount
import WE05SixthMajorRoot

noncomputable section
namespace WuSource.SrcSixthGain
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu2008DoubleSieve Wu08TerminalAlignment NodeExtension ActualNineFeedback
open PositiveTwoPayment PositiveCoreResume PositiveSecondPayment Wu08OriginalFourWeights
open scoped Classical BigOperators

def transferred (x : Fin 9 → ℝ) : Fin 21 → ℝ := matrixApply transferMatrix x

def sourceNet (w : Fin 21 → ℝ) : ℝ :=
  8*(∑ j : Fin 21, g6Weight j*w j)-highLoss w+HighConsumer.highGain

def conservative (w : Fin 21 → ℝ) : ℝ :=
  max (∑ j : Fin 21, WuTarget.W03.paidWeights j*w j)
    (8*(∑ j : Fin 21, g6Weight j*w j)-(16129:ℝ)/40000*heightCap w) +
    (4403217/699329000000 : ℝ)

def sourceCoefficient (g6 : ℝ) : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+
    8*secondGain+fifthGain+g6+4*Phase20.rawPsi+4*Phase18.g18)/4

theorem sourceNet_exact (w : Fin 21 → ℝ) :
    sourceNet w = Gamma w 0+HighConsumer.highGain := by
  unfold sourceNet
  rw [full_weights_same_profile_debit]

theorem conservative_le_net {w : Fin 21 → ℝ} (hn : ∀ j, 0 ≤ w j) :
    conservative w ≤ sourceNet w := by
  rw [sourceNet_exact]
  exact add_le_add (max_le (WuTarget.W03.paid_weights_consumer hn) (full_weights_capped w))
    WuTarget.W15.highGain_rational

theorem net_le_consumed {x : Fin 9 → ℝ} {w : Fin 21 → ℝ}
    (hw : ∀ j, w j ≤ transferred x j) :
    sourceNet w ≤ WuTarget.W01.lowGain x+HighConsumer.highGain := by
  rw [sourceNet_exact]
  change Gamma w 0+HighConsumer.highGain ≤ Gamma (transferred x) 0+HighConsumer.highGain
  linarith only [Gamma_mono hw (t := 0) le_rfl]

theorem conservative_le_consumed {x : Fin 9 → ℝ} {w : Fin 21 → ℝ}
    (hn : ∀ j, 0 ≤ w j) (hw : ∀ j, w j ≤ transferred x j) :
    conservative w ≤ WuTarget.W01.lowGain x+HighConsumer.highGain :=
  (conservative_le_net hn).trans (net_le_consumed hw)

theorem conservative_nonneg {w : Fin 21 → ℝ} (hn : ∀ j, 0 ≤ w j) :
    (4403217/699329000000 : ℝ) ≤ conservative w := by
  have hsum : 0 ≤ ∑ j : Fin 21, WuTarget.W03.paidWeights j*w j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (WuTarget.W03.paidWeights_pos j).le (hn j))
  unfold conservative
  linarith only [hsum,le_max_left
    (∑ j : Fin 21, WuTarget.W03.paidWeights j*w j)
    (8*(∑ j : Fin 21, g6Weight j*w j)-(16129:ℝ)/40000*heightCap w)]

theorem coefficient_exact (x : Fin 9 → ℝ) :
    sourceCoefficient (WuTarget.W01.lowGain x+HighConsumer.highGain) =
      WuTarget.W01.ordinaryCoefficient x := by
  unfold sourceCoefficient WuTarget.W01.ordinaryCoefficient
  ring

theorem coefficient_mono {a b : ℝ} (h : a ≤ b) :
    sourceCoefficient a ≤ sourceCoefficient b := by
  unfold sourceCoefficient
  linarith only [h]

theorem actual_sixth {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 eps : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i)
    (heps : 0 < eps) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ delta : ℝ, 0 < delta → delta < d →
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (sixthMain+conservative w-eps)*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨d,hd,hdd0,hdhi,hbound⟩ := WuTarget.W01.actual_sixth hx0 hd0 hx heps
  refine ⟨d,hd,hdd0,hdhi,?_⟩
  intro delta hdelta hdelta'
  obtain ⟨T,hT,hcount⟩ := hbound delta hdelta hdelta'
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hM := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right
    (show sixthMain+conservative w-eps ≤
      truncatedSixthLowerF6lin+WuTarget.W01.lowGain x+HighConsumer.highGain-eps by
      change truncatedSixthLowerF6lin+conservative w-eps ≤ _
      linarith only [conservative_le_consumed hw0 hw]) hM).trans (hcount N hN he)

theorem sixth_lower {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i) :
    SixthSlotAssembly.SixthLower (conservative w) := by
  intro eps heps
  obtain ⟨d,hd,_,_,hb⟩ := actual_sixth hx0 hw0 hw hd0 hx heps
  obtain ⟨T,hT,hc⟩ := hb (d/2) (half_pos hd) (half_lt_self hd)
  refine ⟨T,hT,?_⟩
  intro N hN he
  simpa only [sixthMain,U8CanonicalMother.M,mul_div_assoc,mul_assoc] using hc N hN he

theorem actual_sixth_classical_lower {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 eps : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i)
    (heps : 0 < eps) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((381/100 : ℝ)+conservative w-eps)*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨d,hd,_,_,hb⟩ := actual_sixth hx0 hw0 hw hd0 hx heps
  obtain ⟨T,hT,hc⟩ := hb (d/2) (half_pos hd) (half_lt_self hd)
  refine ⟨T,hT,?_⟩
  intro N hN he
  exact (mul_le_mul_of_nonneg_right
    (by linarith only [WuTarget.E05SixthMajor.actual_sixth_target] :
      (381/100 : ℝ)+conservative w-eps ≤ sixthMain+conservative w-eps)
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le).trans (hc N hN he)

theorem ordinary_count {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 eps dmax : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i)
    (heps : 0 < eps) (hdmax : 0 < dmax) :
    ∃ delta : ℝ, 0 < delta ∧ delta < dmax ∧ delta < d0 ∧ delta ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (sourceCoefficient (conservative w)-eps)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨delta,hd,hdm,hd0',hdhi,T,hT,hcount⟩ :=
    WuTarget.W01.ordinary_P2 hx0 hd0 hx heps hdmax
  refine ⟨delta,hd,hdm,hd0',hdhi,T,hT,?_⟩
  intro N hN he
  have hc := coefficient_mono (conservative_le_consumed hw0 hw)
  rw [coefficient_exact] at hc
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc eps)
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le).trans (hcount N hN he)

theorem transferred_source_lower {x : Fin 9 → ℝ} {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10) (hx : ∀ i, x i ≤ actualNine delta i) :
    8*(∑ j : Fin 21, g6Weight j*transferred x j) ≤ originalReduced delta :=
  original_reduced_lower hd hdhi (WuTarget.W01.transferred_actual hd hdhi hx)

#print axioms sixth_lower
#print axioms actual_sixth_classical_lower
#print axioms ordinary_count
#print axioms transferred_source_lower
end WuSource.SrcSixthGain
