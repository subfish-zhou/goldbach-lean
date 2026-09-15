import W13TightScalar

noncomputable section
open Real Wu2008DoubleSieve Wu08OriginalFourWeights Wu08TerminalAlignment
open PositiveSecondPayment PositiveCoreResume

namespace WuTarget.W13Tight

def paidQ : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-pairUpper+
    8*secondGain+fifthGain+FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18)/4

theorem paidQ_identity :
    paidQ = Wu08FourMother.Qoriginal+(original10+original11-pairUpper)/4 := by
  unfold paidQ Wu08FourMother.Qoriginal
  ring

theorem paidQ_le_Qoriginal : paidQ ≤ Wu08FourMother.Qoriginal := by
  rw [paidQ_identity]
  linarith only [original_pair_upper]

theorem paidQ_recovery :
    paidQ-W13.paidQ = (W13.pairUpper-pairUpper)/4 := by
  rw [paidQ_identity, W13.paidQ_identity]
  ring

theorem paidQ_strict : W13.paidQ < paidQ := by
  have hp := pair_strict
  rw [← sub_pos, paidQ_recovery]
  linarith only [hp]

theorem paidQ_gain : W13.paidQ+2457/1000000 < paidQ := by
  have hr := paidQ_recovery
  linarith only [hr, recovery_lower]

theorem actual_pair_upper {σ : ℝ} (hσ : 0 < σ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        (pairUpper+σ)*U8CanonicalMother.M N := by
  obtain ⟨T,_,hN⟩ := Wu08FourMother.original_pair_paid hσ
  refine ⟨max T 512,by omega,fun N hn he => ?_⟩
  have hp := hN N (by omega) he
  rw [Wu08FourMother.originalIntegral_false, Wu08FourMother.originalIntegral_true] at hp
  have hm0 : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (by omega)).le
  exact hp.trans (mul_le_mul_of_nonneg_right
    (add_le_add original_pair_upper (le_refl σ)) hm0)

theorem paid_parameters {ζ ξmax : ℝ} (hζ : 0 < ζ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧
      ∀ dmax : ℝ, 0 < dmax →
      ∃ δ η ρ ε : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
        0 < η ∧ η < 1/8 ∧ 1 < ρ ∧ ρ ≤ 5/4 ∧
        0 < ε ∧ ε < truncatedSixthLowerAlpha ∧ ε < δ ∧
      ∀ A : ℕ, ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
          (pairUpper+ζ/2)*U8CanonicalMother.M N+(N : ℝ)/log N^A) ∧
        ((Wu08FourMother.Qoriginal-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) ∧
        ((paidQ-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨ξ,hξ,hξu,h⟩ := Wu08FourMother.ordinary_P2_parameters hζ hmax
  refine ⟨ξ,hξ,hξu,fun dmax hdmax => ?_⟩
  obtain ⟨δ,η,ρ,ε,hδ,hδm,hδu,hη,hηu,hρ,hρu,hε,hεa,hεδ,hA⟩ := h dmax hdmax
  refine ⟨δ,η,ρ,ε,hδ,hδm,hδu,hη,hηu,hρ,hρu,hε,hεa,hεδ,fun A => ?_⟩
  obtain ⟨T,hT,hN⟩ := hA A
  refine ⟨T,hT,fun N hn he => ?_⟩
  obtain ⟨hp,hc⟩ := hN N hn he
  have hm0 : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (by omega)).le
  rw [Wu08FourMother.originalIntegral_false, Wu08FourMother.originalIntegral_true] at hp
  refine ⟨hp.trans (add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add original_pair_upper (le_refl (ζ/2))) hm0) (le_refl _)), hc, ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right paidQ_le_Qoriginal ζ) hm0).trans hc

theorem paid_ordinary_P2 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidQ-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨_,_,_,h⟩ := paid_parameters hζ (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨δ,_,_,_,hδ,_,hδu,_,_,_,_,_,_,_,hA⟩ := h (1/100) (by norm_num)
  obtain ⟨T,hT,hN⟩ := hA 3
  exact ⟨δ,hδ,hδu,T,hT,fun N hn he => (hN N hn he).2.2⟩

end WuTarget.W13Tight
