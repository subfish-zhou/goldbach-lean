import W01WeightedNormalization

noncomputable section
namespace WuTarget.W01
open Wu2008DoubleSieve Wu08TerminalAlignment NodeExtension Filter
open PositiveTwoPayment PositiveCoreResume PositiveSecondPayment Wu08OriginalFourWeights
open scoped Classical Topology

/-- Original signed numerator, with the finite low gain and the disjoint high gain each once. -/
def ordinaryCoefficient (x : Fin 9 → ℝ) : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+
    8*secondGain+fifthGain+lowGain x+4*Phase20.rawPsi+4*Phase18.g18+
    HighConsumer.highGain)/4

/-- This identity cancels Cinf; it does not compare the input vector with Ainf. -/
theorem ordinaryCoefficient_eq (x : Fin 9 → ℝ) :
    ordinaryCoefficient x = Wu08FourMother.Qoriginal+
      (lowGain x-FeedbackLimit.Cinf+HighConsumer.highGain)/4 := by
  unfold ordinaryCoefficient Wu08FourMother.Qoriginal
  ring

theorem ordinaryCoefficient_mono {x y : Fin 9 → ℝ} (hxy : ∀ i, x i ≤ y i) :
    ordinaryCoefficient x ≤ ordinaryCoefficient y := by
  have h := lowGain_mono hxy
  unfold ordinaryCoefficient
  linarith only [h]

theorem coefficient_cap (x : Fin 9 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < a →
      4*ordinaryCoefficient x-ε ≤
        FullLogMother.psiCoefficient δ+lowGain x+HighConsumer.highGain-
          FullSourceLog.GammaLog6+increment secondGain fifthGain+
          Wu08FourMother.restoredDebit+8*U8CanonicalMother.L-8*U8CanonicalMother.I := by
  obtain ⟨a,ha,ha1,hcoef⟩ := Wu08FourMother.coefficient_cap hε
  refine ⟨a,ha,ha1,?_⟩
  intro δ hδ hδa
  have h := hcoef δ hδ hδa
  rw [ordinaryCoefficient_eq]
  linarith only [h]

/-- Actual ordinary-P2 carrier; the original pair producer chooses one delta below every cap. -/
theorem ordinary_P2 {x : Fin 9 → ℝ} {d0 ε dmax : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ < d0 ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (ordinaryCoefficient x-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨η,hη,hη1,b,hb,hb0,_,hm⟩ := mixed_normalization hn hd0 hx hε
  obtain ⟨a,ha,_,hcoef⟩ := coefficient_cap x hε
  obtain ⟨_,_,_,hpair⟩ :=
    Wu08FirstPrimeFour.SmallBoundaryRecovery.original_pair_integral_parameters
      (half_pos hε) (show (0 : ℝ) < 1/2 by norm_num)
  let cap := min dmax (min b (min a (min (1/100) (50*HighBoxRecovery.highEta))))
  have hcap : 0 < cap := by
    dsimp [cap]
    exact lt_min hdmax (lt_min hb (lt_min ha
      (lt_min (by norm_num) (by norm_num [HighBoxRecovery.highEta]))))
  obtain ⟨δ,_,_,_,hδ,hδcap,_,_,_,_,_,_,_,_,hraw⟩ := hpair cap hcap
  have hmax : δ < dmax := hδcap.trans_le (min_le_left _ _)
  have hdb : δ < b := hδcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hda : δ < a :=
    hδcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : δ < min (1/100) (50*HighBoxRecovery.highEta) :=
    hδcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hd : δ < 1/100 := hsmall.trans_le (min_le_left _ _)
  have hdhi : δ ≤ 50*HighBoxRecovery.highEta := hsmall.le.trans (min_le_right _ _)
  have pair : Wu08FourMother.PairUpper ε := by
    obtain ⟨Tq,_,hq⟩ := hraw 3
    obtain ⟨Tr,_,hr⟩ := Wu08FourMother.raw_error_paid (half_pos hε)
    obtain ⟨Tn,hTn⟩ := exists_nat_ge Tq
    refine ⟨max 4 (max Tn Tr),le_max_left _ _,?_⟩
    intro N hN he
    have hqN := hq N (hTn.trans (by exact_mod_cast (show Tn ≤ N by omega))) he
    have hrN := hr N (by omega)
    change _ ≤ _*U8CanonicalMother.M N+_ at hqN
    linarith only [hqN,hrN]
  obtain ⟨n,hn⟩ := (hm δ hδ hdb).exists
  obtain ⟨Tm,hTm⟩ := eventually_atTop.mp hn
  obtain ⟨Tc,hTc,hcount⟩ := HighConsumer.signed_mixed pair hδ hdhi hd hη hη1 hε
    (MixedSixth.lowNodes δ n) (MixedSixth.lowNodes_bounds hδ.le n)
  refine ⟨δ,hδ,hmax,hdb.trans_le hb0,hd.le,max Tm Tc,
    hTc.trans (le_max_right _ _),?_⟩
  intro N hN he
  have hNc : Tc ≤ N := (le_max_right _ _).trans hN
  have hN512 := hTc.trans hNc
  have hN1 : 1 < N := by omega
  have hc := hcount N hNc he (truncatedSixthMassDelta N)
    (truncatedSixthMass_delta_legal hN1).2.1 (truncatedSixthMass_delta_legal hN1).2.2
    _ _ _ _ _ _ _ _ (MixedSixth.actual_geometry hN1 hδ.le n)
  have hmN := hTm N ((le_max_left _ _).trans hN)
  change (truncatedSixthLowerF6lin+lowGain x+HighConsumer.highGain-ε)*
    U8CanonicalMother.M N ≤ MixedSixth.main N n δ η at hmN
  have hM := (HighSixPhase6.original_scale_positive hN512).le
  change 0 ≤ U8CanonicalMother.M N at hM
  have hscaled := mul_le_mul_of_nonneg_right (hcoef δ hδ hda) hM
  change _ + MixedSixth.main N n δ η ≤
    4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
      ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hc
  nlinarith only [hc,hmN,hscaled]

theorem v8_lowGain_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d →
      lowGain Wu04Bypass.v8-ε ≤ truncatedSixthLowerHadmdelta δ := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  obtain ⟨d,hd,_,hdhi,h⟩ := lowGain_Hadm_payment
    (fun i => (Wu04Bypass.new_vector_positive i).le) hd0 hx hε
  exact ⟨d,hd,hdhi,h⟩

/-- Frozen v8 is actually consumed, without any table, matrix or integral-value premise. -/
theorem v8_ordinary_P2 {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, Wu04Bypass.v8 i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, ActualNineFeedback.matrixApply transferMatrix Wu04Bypass.v8 j ≤
        wuImprovementLimit false δ (rNode (j.val+1))) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (ordinaryCoefficient Wu04Bypass.v8-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  obtain ⟨δ,hδ,hmax,hδ0,hdhi,T,hT,h⟩ := ordinary_P2
    (fun i => (Wu04Bypass.new_vector_positive i).le) hd0 hx hε hdmax
  have hnodes := hx δ hδ hδ0.le
  exact ⟨δ,hδ,hmax,hdhi,hnodes,
    transferred_actual hδ (by linarith) hnodes,T,hT,h⟩

end WuTarget.W01
