import MixedFinalNormalization

namespace MixedFinal
open Wu2008DoubleSieve Filter HighBoxRecovery
open scoped Topology
noncomputable section

/-- Full sixth-slot scalar, with no grid, mass, or gain premise left over. -/
theorem actual_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d →
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (truncatedSixthLowerF6lin+FeedbackLimit.Cinf+HighConsumer.highGain-ε)*
          U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨η,hη,hη1,a,ha,ha1,hm⟩ := normalization (half_pos hε)
  refine ⟨min a (50*highEta),lt_min ha (by norm_num [highEta]),
    (min_le_left _ _).trans ha1,?_⟩
  intro δ hδ hδd
  have hda := hδd.trans_le (min_le_left _ _)
  have hdhi := hδd.le.trans (min_le_right _ _)
  obtain ⟨n,hn⟩ := (hm δ hδ hda).exists
  obtain ⟨Tm,hTm⟩ := eventually_atTop.mp hn
  obtain ⟨Tc,hTc,hc⟩ := MixedSixth.actual_count hδ hdhi (hda.trans_le ha1)
    hη hη1 (half_pos hε) n
  refine ⟨max Tm Tc,hTc.trans (le_max_right _ _),?_⟩
  intro N hN he
  have hmN := hTm N (le_trans (le_max_left _ _) hN)
  have hcN := hc N (le_trans (le_max_right _ _) hN) he
  change (truncatedSixthLowerF6lin+FeedbackLimit.Cinf+HighConsumer.highGain-ε/2)*
    U8CanonicalMother.M N ≤ MixedSixth.main N n δ η at hmN
  linarith only [hmN,hcN]

/-- Original ordinary-P2 count. F10/F11 is paid once in the same signed mother;
the high improvement enters only through replacement of its actual sixth slot. -/
theorem ordinary_P2 {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Wu08FourMother.Qoriginal+HighConsumer.highGain/4-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨η,hη,hη1,b,hb,_,hm⟩ := normalization hε
  obtain ⟨a,ha,_,hcoef⟩ := Wu08FourMother.coefficient_cap hε
  obtain ⟨_,_,_,hpair⟩ := Wu08FirstPrimeFour.SmallBoundaryRecovery.original_pair_integral_parameters
    (half_pos hε) (show (0 : ℝ) < 1/2 by norm_num)
  let cap := min dmax (min b (min a (min (1/100) (50*highEta))))
  have hcap : 0 < cap := by
    dsimp [cap]
    exact lt_min hdmax (lt_min hb (lt_min ha (lt_min (by norm_num) (by norm_num [highEta]))))
  obtain ⟨δ,_,_,_,hδ,hδcap,_,_,_,_,_,_,_,_,hraw⟩ := hpair cap hcap
  have hmax : δ < dmax := hδcap.trans_le (min_le_left _ _)
  have hdb : δ < b := hδcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hda : δ < a := hδcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : δ < min (1/100) (50*highEta) :=
    hδcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hd : δ < 1/100 := hsmall.trans_le (min_le_left _ _)
  have hdhi : δ ≤ 50*highEta := hsmall.le.trans (min_le_right _ _)
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
  refine ⟨δ,hδ,hmax,hd.le,max Tm Tc,hTc.trans (le_max_right _ _),?_⟩
  intro N hN he
  have hNc : Tc ≤ N := (le_max_right _ _).trans hN
  have hN512 := hTc.trans hNc
  have hN1 : 1 < N := by omega
  have hc := hcount N hNc he (truncatedSixthMassDelta N)
    (truncatedSixthMass_delta_legal hN1).2.1 (truncatedSixthMass_delta_legal hN1).2.2
    _ _ _ _ _ _ _ _ (MixedSixth.actual_geometry hN1 hδ.le n)
  have hmN := hTm N ((le_max_left _ _).trans hN)
  change (truncatedSixthLowerF6lin+FeedbackLimit.Cinf+HighConsumer.highGain-ε)*
    U8CanonicalMother.M N ≤ MixedSixth.main N n δ η at hmN
  have hM := (HighSixPhase6.original_scale_positive hN512).le
  change 0 ≤ U8CanonicalMother.M N at hM
  have hscaled := mul_le_mul_of_nonneg_right (hcoef δ hδ hda) hM
  change _ + MixedSixth.main N n δ η ≤
    4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
      ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hc
  nlinarith only [hc,hmN,hscaled]

end
end MixedFinal
