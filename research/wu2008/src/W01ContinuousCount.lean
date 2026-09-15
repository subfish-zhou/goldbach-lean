import W01ContinuousLoss

noncomputable section
namespace WuTarget.W01Continuous
open Wu2008DoubleSieve Wu08TerminalAlignment NodeExtension Filter
open PositiveTwoPayment PositiveCoreResume PositiveSecondPayment Wu08OriginalFourWeights
open scoped Classical Topology

def continuousCoefficient (x : Fin 9 → ℝ) : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+
    8*secondGain+fifthGain+continuousGain x+4*Phase20.rawPsi+4*Phase18.g18+
    HighConsumer.highGain)/4

theorem continuousCoefficient_eq (x : Fin 9 → ℝ) :
    continuousCoefficient x = WuTarget.W01.ordinaryCoefficient x+
      (continuousGain x-WuTarget.W01.lowGain x)/4 := by
  unfold continuousCoefficient WuTarget.W01.ordinaryCoefficient
  ring

theorem old_coefficient_le_continuous {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    WuTarget.W01.ordinaryCoefficient x ≤ continuousCoefficient x := by
  rw [continuousCoefficient_eq]
  exact le_add_of_nonneg_right (div_nonneg
    (sub_nonneg.mpr (lowGain_le_continuousGain hx)) (by norm_num))

theorem continuous_B_normalization {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (truncatedSixthLowerF6lin+continuousGain x-ε)*truncatedSixthMassScale N ≤
          LowComplement.B N n δ := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,hahi,hFa⟩ := truncatedSixthZeroDelta_Fdelta_close he
  obtain ⟨b,hb,hb0,_,hHb⟩ := continuousGain_Hadm_payment hn hd0 hx he
  refine ⟨min a b,lt_min ha hb,(min_le_right _ _).trans hb0,
    (min_le_left _ _).trans hahi,?_⟩
  intro δ hδ hδd
  have hδa := hδd.trans_le (min_le_left a b)
  have hδb := hδd.trans_le (min_le_right a b)
  have hF := (abs_lt.mp (hFa δ hδ hδa)).1
  have hH := hHb δ hδ hδb
  filter_upwards [LowComplement.B_delta_normalization hδ (hδa.trans_le hahi) he] with n hn
  filter_upwards [hn,eventually_ge_atTop (4:ℕ)] with N hN hN4
  exact (mul_le_mul_of_nonneg_right (by linarith only [hF,hH])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

theorem continuous_mixed_normalization {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
        ∀ δ : ℝ, 0 < δ → δ < d → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          (truncatedSixthLowerF6lin+continuousGain x+HighConsumer.highGain-ε)*
            truncatedSixthMassScale N ≤ MixedSixth.main N n δ η := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,ha0,hahi,hB⟩ := continuous_B_normalization hn hd0 hx he
  obtain ⟨b,hb,hE⟩ := HighIncrement.actual_highGain_lower he
  obtain ⟨η,hη,hη1,hpay⟩ := LowComplement.uniform_eta_payment_capped he
  refine ⟨η,hη,hη1,min a b,lt_min ha hb,
    (min_le_left _ _).trans ha0,(min_le_left _ _).trans hahi,?_⟩
  intro δ hδ hδd
  obtain ⟨n0,hn0⟩ := hE δ hδ.le (hδd.le.trans (min_le_right _ _))
  have hEn := eventually_atTop.mpr ⟨n0,hn0⟩
  filter_upwards [hB δ hδ (hδd.trans_le (min_le_left _ _)),hEn] with n hBn hEn
  filter_upwards [hBn,hEn,hpay] with N hBN hEN hηN
  have hp := hηN δ hδ.le n
  unfold LowComplement.B at hBN
  linarith only [hBN,hEN,hp]

theorem continuous_coefficient_cap (x : Fin 9 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < a →
      4*continuousCoefficient x-ε ≤
        FullLogMother.psiCoefficient δ+continuousGain x+HighConsumer.highGain-
          FullSourceLog.GammaLog6+increment secondGain fifthGain+
          Wu08FourMother.restoredDebit+8*U8CanonicalMother.L-8*U8CanonicalMother.I := by
  obtain ⟨a,ha,ha1,hcoef⟩ := WuTarget.W01.coefficient_cap x hε
  refine ⟨a,ha,ha1,?_⟩
  intro δ hδ hδa
  have h := hcoef δ hδ hδa
  rw [continuousCoefficient_eq]
  linarith only [h]

/-- The continuous Hadm payment is constructed above and consumed in the original signed mother. -/
theorem continuous_ordinary_P2 {x : Fin 9 → ℝ} {d0 ε dmax : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ < d0 ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (continuousCoefficient x-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨η,hη,hη1,b,hb,hb0,_,hm⟩ := continuous_mixed_normalization hn hd0 hx hε
  obtain ⟨a,ha,_,hcoef⟩ := continuous_coefficient_cap x hε
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
  change (truncatedSixthLowerF6lin+continuousGain x+HighConsumer.highGain-ε)*
    U8CanonicalMother.M N ≤ MixedSixth.main N n δ η at hmN
  have hM := (HighSixPhase6.original_scale_positive hN512).le
  change 0 ≤ U8CanonicalMother.M N at hM
  have hscaled := mul_le_mul_of_nonneg_right (hcoef δ hδ hda) hM
  change _ + MixedSixth.main N n δ η ≤
    4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
      ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hc
  nlinarith only [hc,hmN,hscaled]

theorem v8_continuousGain_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d →
      continuousGain Wu04Bypass.v8-ε ≤ truncatedSixthLowerHadmdelta δ := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  obtain ⟨d,hd,_,hdhi,h⟩ := continuousGain_Hadm_payment
    (fun i => (Wu04Bypass.new_vector_positive i).le) hd0 hx hε
  exact ⟨d,hd,hdhi,h⟩

theorem v8_continuous_ordinary_P2 {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, Wu04Bypass.v8 i ≤ actualNine δ i) ∧
      (∀ s ∈ Set.Icc (2:ℝ) (41/10),
        hContinuous Wu04Bypass.v8 s ≤ wuImprovementLimit false δ s) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (continuousCoefficient Wu04Bypass.v8-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  obtain ⟨δ,hδ,hmax,hδ0,hdhi,T,hT,h⟩ := continuous_ordinary_P2
    (fun i => (Wu04Bypass.new_vector_positive i).le) hd0 hx hε hdmax
  have hnodes := hx δ hδ hδ0.le
  exact ⟨δ,hδ,hmax,hdhi,hnodes,
    fun _ hs => hContinuous_le_actual hδ (by linarith) hnodes hs,T,hT,h⟩

theorem v8_old_gain_le_continuous :
    WuTarget.W01.lowGain Wu04Bypass.v8 ≤ continuousGain Wu04Bypass.v8 :=
  lowGain_le_continuousGain (fun i => (Wu04Bypass.new_vector_positive i).le)

theorem v8_old_coefficient_le_continuous :
    WuTarget.W01.ordinaryCoefficient Wu04Bypass.v8 ≤ continuousCoefficient Wu04Bypass.v8 :=
  old_coefficient_le_continuous (fun i => (Wu04Bypass.new_vector_positive i).le)

end WuTarget.W01Continuous
