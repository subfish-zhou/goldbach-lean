import Wu08FourMotherCounts

noncomputable section
open Real Wu2008DoubleSieve U8CanonicalMother
namespace Wu08FourMother
open Wu08OriginalFourWeights Wu08TerminalAlignment
open PositiveTwoPayment PositiveCoreResume PositiveSecondPayment
open Wu08FirstPrimeFour.SmallBoundaryRecovery

/-- Original F10/F11 replace the unit-weight amounts. This definition alone is
not a count theorem; ordinary_P2_parameters below consumes the actual producer. -/
def Qoriginal : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+
    8*secondGain+fifthGain+FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18)/4

theorem coefficient_exact : Qoriginal = Qtwo+restoredDebit/4 := by
  rw [Qtwo_original_weight_debits]
  unfold Qoriginal restoredDebit
  ring

theorem Qtwo_le_original : Qtwo ≤ Qoriginal := by
  rw [coefficient_exact]
  linarith only [restoredDebit_nonneg]

/-- Uniform small-delta payment, using only the existing classical/Psi limit
and the paid H linear error. No continuity or monotonicity of H/h is asserted. -/
theorem coefficient_cap {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < a →
      4*Qoriginal-ε ≤ FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-
        FullSourceLog.GammaLog6+increment secondGain fifthGain+restoredDebit+8*L-8*I := by
  have herror := Phase18.B18_pos
  obtain ⟨a,ha,ha1,hclose⟩ := HighSixDeltaLimit.coefficient_close
    (show 0 < ε/3 by positivity)
  let b : ℝ := min (a/2) (ε/(12*(Phase18.B18+1)))
  have hb : 0 < b := lt_min (half_pos ha) (div_pos hε (by positivity))
  have hba : b < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  refine ⟨b,hb,hba.le.trans ha1,fun δ hδ hδb => ?_⟩
  have hδa : δ < a := hδb.trans hba
  have hδhi : δ ≤ 1/100 := hδa.le.trans ha1
  have hδpay : δ ≤ ε/(12*(Phase18.B18+1)) :=
    hδb.le.trans (min_le_right _ _)
  have hpay : 12*(Phase18.B18+1)*δ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(Phase18.B18+1))).mp hδpay
    nlinarith only [hh]
  have hbudget : 4*Phase18.B18*δ ≤ ε/3 := by nlinarith only [hpay,hδ]
  have hcoef := (abs_lt.mp (hclose δ hδ hδa)).1
  have hh := Phase18.gain18_linear_error hδ hδhi
  rw [FullLogCount.fixed_same_mother_identity,coefficient_exact,Qtwo_eq_Qof]
  unfold Qof FeedbackLimit.Qinf LogP2.Qlog Phase20.unroundedCoefficient
  linarith only [hcoef,hh,hbudget,hε]

/-- The full original Q10/Q11 parameter contract and the actual ordinary-P2
count use the SAME delta. Xi is selected first, then every prescribed positive
cap admits one common delta, finally A and N. The raw remainder is displayed
for every A and independently paid at A=3 in the count endpoint. -/
theorem ordinary_P2_parameters {ζ ξmax : ℝ} (hζ : 0 < ζ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧
      ∀ dmax : ℝ, 0 < dmax →
      ∃ δ η ρ ε : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
        0 < η ∧ η < 1/8 ∧ 1 < ρ ∧ ρ ≤ 5/4 ∧
        0 < ε ∧ ε < truncatedSixthLowerAlpha ∧ ε < δ ∧
      ∀ A : ℕ, ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
          (originalIntegral false+originalIntegral true+ζ/2)*U8CanonicalMother.M N+(N : ℝ)/log N^A) ∧
        ((Qoriginal-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨ξ,hξ,hξu,hpair⟩ := original_pair_integral_parameters (half_pos hζ) hmax
  refine ⟨ξ,hξ,hξu,?_⟩
  intro dmax hdmax
  obtain ⟨a,ha,ha1,hcoef⟩ := coefficient_cap hζ
  obtain ⟨δ,η,ρ,ε,hδ,hδcap,_,hη,hηu,hρ,hρu,hε,hεa,hεδ,hraw⟩ :=
    hpair (min dmax a) (lt_min hdmax ha)
  have hδm : δ < dmax := hδcap.trans_le (min_le_left _ _)
  have hδa : δ < a := hδcap.trans_le (min_le_right _ _)
  have hδhi : δ ≤ 1/100 := hδa.le.trans ha1
  have paidPair : PairUpper ζ := by
    obtain ⟨Tq,_,hq⟩ := hraw 3
    obtain ⟨Tr,_,hr⟩ := raw_error_paid (half_pos hζ)
    obtain ⟨Tn,hTn⟩ := exists_nat_ge Tq
    refine ⟨max (max Tn Tr) 4,by omega,fun N hN he => ?_⟩
    have hqN := hq N (hTn.trans (by exact_mod_cast (show Tn ≤ N by omega))) he
    have hrN := hr N (by omega)
    change _ ≤ _*U8CanonicalMother.M N+_ at hqN
    linarith only [hqN,hrN]
  obtain ⟨Tc,hTc,hcount⟩ := signed_count paidPair hδ hδhi hζ
  refine ⟨δ,η,ρ,ε,hδ,hδm,hδhi,hη,hηu,hρ,hρu,hε,hεa,hεδ,?_⟩
  intro A
  obtain ⟨Ta,_,hA⟩ := hraw A
  obtain ⟨Tn,hTn⟩ := exists_nat_ge Ta
  refine ⟨max Tc Tn,by omega,fun N hN he => ?_⟩
  constructor
  · exact hA N (hTn.trans (by exact_mod_cast (show Tn ≤ N by omega))) he
  · have hc := hcount N (by omega) he
    have hm0 : 0 ≤ U8CanonicalMother.M N := (HighSixPhase6.original_scale_positive (by omega)).le
    have hco : 4*Qoriginal-4*ζ ≤ FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-
        FullSourceLog.GammaLog6+increment secondGain fifthGain+restoredDebit+8*L-8*I-ζ-ζ := by
      have := hcoef δ hδ hδa
      linarith only [this,hζ]
    have hm := (mul_le_mul_of_nonneg_right hco hm0).trans hc
    change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
      ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hm
    nlinarith only [hm]

/-- Concrete count endpoint, with both recovered Q inputs and all positive
producers constructed. Complement 1 is permitted, 0 excluded, Ω counted with
multiplicity, and there is no extra relative-size condition. -/
theorem ordinary_P2 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qoriginal-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨_,_,_,hp⟩ := ordinary_P2_parameters hζ (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨δ,_,_,_,hδ,_,hd,_,_,_,_,_,_,_,h⟩ := hp (1/100) (by norm_num)
  obtain ⟨T,hT,hN⟩ := h 3
  exact ⟨δ,hδ,hd,T,hT,fun N hn he => (hN N hn he).2⟩

end Wu08FourMother
