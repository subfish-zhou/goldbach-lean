import LogU8Residual
import U8CanonicalMother

noncomputable section
open Finset Real
open Wu2008DoubleSieve U8CanonicalMother
namespace LogP2
/-- Both real producers choose their thresholds before the common even N. -/
theorem ordinary_replacement {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ + 8*L - 8*I - ε) * U8CanonicalMother.M N ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨Tm,hTm,hm⟩ := LogU8Residual.ordinary_small_debit hδ hδhi (half_pos hε)
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/2) (half_pos hε)
  refine ⟨max Tm Ts,hTm.trans (le_max_left _ _),?_⟩
  intro N hN heven
  have hmN := hm N ((le_max_left _ _).trans hN) heven
  have hsN := hs N ((le_max_right _ _).trans hN) heven
  have h512 : 512 ≤ N := hTm.trans ((le_max_left _ _).trans hN)
  have hnorm := scale_eq_liu (show 0 < N by omega)
  rw [← small_eq_physicalSmall] at hsN
  rw [← L_eq_oldSmallIntegral] at hmN
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤ (8*I+ε/2)*U8CanonicalMother.M N := by
    rw [hnorm]
    convert hsN using 1
    ring
  have hmM : (FullLogMother.psiCoefficient δ+8*L-ε/2)*U8CanonicalMother.M N -
      ((U8MotherInsertion.small N).card : ℝ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    convert hmN using 1
    dsimp [U8CanonicalMother.M]
    ring
  nlinarith only [hmM,hsM]

open SingleUpperHIntegral HighSixDeltaLimit

def Qlog : ℝ := Phase20.unroundedCoefficient +
  (2*BaseHGain.originalGain+fifthHGain/4) +
  (FullSourceLog.GammaLog6-47/481250)/4 + 2*(L-I)

/-- Delta is chosen directly from the coefficient limit, not from an old lower bound. -/
theorem same_mother_delta_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (limitCoefficient+4*Phase18.g18+
          (8*BaseHGain.originalGain+fifthHGain+(FullSourceLog.GammaLog6-47/481250))+
          8*L-8*I-ε)*U8CanonicalMother.M N ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have herror := Phase18.B18_pos
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,ha1,hclose⟩ := coefficient_close he
  let δ : ℝ := min (a/2) (ε/(12*(Phase18.B18+1)))
  have hδ : 0 < δ := lt_min (half_pos ha) (div_pos hε (by positivity))
  have hδa : δ < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hδhi : δ ≤ 1/100 := hδa.le.trans ha1
  have hδb : δ ≤ ε/(12*(Phase18.B18+1)) := min_le_right _ _
  have hpay : 12*(Phase18.B18+1)*δ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(Phase18.B18+1))).mp hδb
    nlinarith only [hh]
  have hbudget : 4*Phase18.B18*δ ≤ ε/3 := by nlinarith only [hpay,hδ]
  have hcoef := (abs_lt.mp (hclose δ hδ hδa)).1
  have hh := Phase18.gain18_linear_error hδ hδhi
  obtain ⟨T,hT,hcount⟩ := ordinary_replacement hδ hδhi he
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN heven
  have hm := hcount N hN heven
  have hc : limitCoefficient+4*Phase18.g18+
      (8*BaseHGain.originalGain+fifthHGain+(FullSourceLog.GammaLog6-47/481250))+
      8*L-8*I-ε ≤ FullLogMother.psiCoefficient δ+8*L-8*I-ε/3 := by
    rw [FullLogCount.fixed_same_mother_identity]
    linarith only [hcoef,hh,hbudget]
  have hs : 0 ≤ U8CanonicalMother.M N := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right hc hs).trans hm

/-- Divide by four exactly once, with no old ordinary lower used. -/
theorem improved_ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qlog-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := same_mother_delta_payment (show 0 < 4*η by positivity)
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hn
  have hid : (Qlog-η)*U8CanonicalMother.M N =
      ((limitCoefficient+4*Phase18.g18+
        (8*BaseHGain.originalGain+fifthHGain+(FullSourceLog.GammaLog6-47/481250))+
        8*L-8*I-4*η)*U8CanonicalMother.M N)/4 := by
    unfold Qlog Phase20.unroundedCoefficient
    ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])

theorem coefficient_identity : Qlog = U8CanonicalMother.improvedCoefficient +
    FullSourceLog.sourceLogGain/4 := by
  unfold Qlog U8CanonicalMother.improvedCoefficient U8CanonicalMother.Q
    FullAdmissibleCount.unroundedCoefficient FullSourceLog.sourceLogGain
  ring

theorem coefficient_difference : Qlog = U8CanonicalMother.improvedCoefficient +
    (FullSourceLog.GammaLog6-FullAdmissibleSeed.Gamma6)/4 := coefficient_identity

theorem coefficient_strict_gain : U8CanonicalMother.improvedCoefficient < Qlog := by
  rw [coefficient_identity]
  have h := FullSourceLog.sourceLogGain_pos
  linarith only [h]

end LogP2
