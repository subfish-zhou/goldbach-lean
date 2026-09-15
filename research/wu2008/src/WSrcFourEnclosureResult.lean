import WSrcFourEnclosureFine

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFourEnclosure

def printedPair : ℝ := 104305/1000000+543858/1000000

theorem printedPair_exact : printedPair = (648163/1000000 : ℝ) := by
  norm_num [printedPair]

theorem original_pair_lower56
    (hl : ∀ u : ℝ, (3 : ℝ) ≤ u → (14/25 : ℝ) ≤ LiLiuPrereqBuchstab.buchstab u) :
    (16959/25000 : ℝ) < original10+original11 := by
  have h := original_pair_lower hl
  have hm := mul_lt_mul_of_pos_left mass_rational_enclosure.1
    (by norm_num : (0 : ℝ) < 14/25)
  linarith only [h,hm]

theorem original_pair_conditional_enclosure
    (hl : ∀ u : ℝ, (3 : ℝ) ≤ u → (14/25 : ℝ) ≤ LiLiuPrereqBuchstab.buchstab u) :
    (16959/25000 : ℝ) < original10+original11 ∧
      original10+original11 < (851/1250 : ℝ) :=
  ⟨original_pair_lower56 hl,original_pair_upper⟩

theorem enclosure_width :
    (851/1250 : ℝ)-16959/25000 = 61/25000 ∧
      (61/25000 : ℝ) < 1/400 := by norm_num

theorem original_pair_unconditional_enclosure :
    (0 : ℝ) ≤ original10+original11 ∧ original10+original11 < (851/1250 : ℝ) :=
  ⟨original_pair_nonneg,original_pair_upper⟩

theorem printed_gap_upper :
    original10+original11-printedPair < (32637/1000000 : ℝ) := by
  rw [printedPair_exact]
  linarith only [original_pair_upper]

theorem printed_gap_conditional
    (hl : ∀ u : ℝ, (3 : ℝ) ≤ u → (14/25 : ℝ) ≤ LiLiuPrereqBuchstab.buchstab u) :
    (30197/1000000 : ℝ) < original10+original11-printedPair ∧
      original10+original11-printedPair < (32637/1000000 : ℝ) := by
  refine ⟨?_,printed_gap_upper⟩
  rw [printedPair_exact]
  linarith only [original_pair_lower56 hl]

theorem printed_pair_not_upper_conditional
    (hl : ∀ u : ℝ, (3 : ℝ) ≤ u → (14/25 : ℝ) ≤ LiLiuPrereqBuchstab.buchstab u) :
    ¬ original10+original11 ≤ printedPair := by
  linarith only [(printed_gap_conditional hl).1]

theorem actual_pair_upper {σ : ℝ} (hσ : 0 < σ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        ((851/1250 : ℝ)+σ)*U8CanonicalMother.M N := by
  obtain ⟨T,_,hN⟩ := Wu08FourMother.original_pair_paid hσ
  refine ⟨max T 512,by omega,fun N hn he => ?_⟩
  have hp := hN N (by omega) he
  rw [Wu08FourMother.originalIntegral_false,Wu08FourMother.originalIntegral_true] at hp
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (by omega)).le
  exact hp.trans (mul_le_mul_of_nonneg_right
    (add_le_add original_pair_upper.le (le_refl σ)) hM)

def enclosedCoefficient : ℝ :=
  Wu08FourMother.Qoriginal+(original10+original11-(851/1250 : ℝ))/4

theorem enclosedCoefficient_exact :
    enclosedCoefficient =
      (3*Wu08TerminalAlignment.firstMain+Wu08TerminalAlignment.secondMain-
        Wu08TerminalAlignment.thirdMain-Wu08TerminalAlignment.fourthMain+
        Wu08TerminalAlignment.fifthMain+Wu08TerminalAlignment.sixthMain-
        2*Wu08TerminalAlignment.seventhMain-Wu08TerminalAlignment.eighthMain-
        Wu08TerminalAlignment.ninthMain-(851/1250 : ℝ)+
        8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain+
        FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18)/4 := by
  unfold enclosedCoefficient Wu08FourMother.Qoriginal
  ring

theorem ordinary_P2_enclosed {ζ dmax : ℝ} (hζ : 0 < ζ) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (enclosedCoefficient-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hcoef : enclosedCoefficient ≤ Wu08FourMother.Qoriginal := by
    unfold enclosedCoefficient
    linarith only [original_pair_upper]
  obtain ⟨_,_,_,hp⟩ := Wu08FourMother.ordinary_P2_parameters hζ
    (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨δ,_,_,_,hδ,hδmax,hδhi,_,_,_,_,_,_,_,h⟩ := hp dmax hdmax
  obtain ⟨T,hT,hN⟩ := h 3
  refine ⟨δ,hδ,hδmax,hδhi,T,hT,fun N hn he => ?_⟩
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hn)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hcoef ζ) hM).trans (hN N hn he).2

#check @original_pair_lower56
#check @original_pair_conditional_enclosure
#check @enclosure_width
#check @original_pair_unconditional_enclosure
#check @printed_gap_conditional
#check @actual_pair_upper
#check @enclosedCoefficient_exact
#check @ordinary_P2_enclosed
#print axioms original_pair_lower56
#print axioms original_pair_conditional_enclosure
#print axioms enclosure_width
#print axioms original_pair_unconditional_enclosure
#print axioms printed_gap_conditional
#print axioms actual_pair_upper
#print axioms enclosedCoefficient_exact
#print axioms ordinary_P2_enclosed
end WuSource.SrcFourEnclosure
