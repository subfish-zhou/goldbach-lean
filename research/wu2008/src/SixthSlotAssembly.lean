import SixthSlotCore

open Real Wu2008DoubleSieve U8CanonicalMother
open Wu2008DoubleSieve.SingleUpperHIntegral Wu2008DoubleSieve.HighSixDeltaLimit

namespace SixthSlotAssembly
noncomputable section

/-- The only combinatorial input slot is an eventual bound for the literal F6 mass. -/
def SixthLower (c : ℝ) : Prop := ∀ ε : ℝ, 0 < ε →
  ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    (truncatedSixthLowerF6lin+c-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      SixthSlotCore.sixth N

/-- Replacement, not addition: the old sixth coefficient is removed once. -/
def Q (c : ℝ) : ℝ := LogP2.Qlog + (c-FullSourceLog.GammaLog6)/4

/-- Same outer delta; the small improvement is paid by its actual producer. -/
theorem ordinary_replacement {c δ ε : ℝ} (h6 : SixthLower c)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ+c-FullSourceLog.GammaLog6+8*L-8*I-ε)*
        U8CanonicalMother.M N ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have heps : 0 < ε/3 := by positivity
  obtain ⟨Tr,hTr,hr⟩ := SixthSlotCore.ordinary_remainder hδ hδhi heps
  obtain ⟨T6,_,h6N⟩ := h6 (ε/3) heps
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/3) heps
  refine ⟨max Tr (max T6 Ts),by omega,?_⟩
  intro N hN he
  have hrN := hr N (by omega) he
  have hfN := h6N N (by omega) he
  have hsN := hs N (by omega) he
  have hnorm := scale_eq_liu (show 0 < N by omega)
  rw [← small_eq_physicalSmall] at hsN
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤
      (8*I+ε/3)*U8CanonicalMother.M N := by
    rw [hnorm]
    convert hsN using 1
    ring
  unfold SixthSlotCore.remainderCoefficient at hrN
  rw [← L_eq_oldSmallIntegral] at hrN
  dsimp [U8CanonicalMother.M] at hsM ⊢
  ring_nf at hrN hfN hsM ⊢
  linarith only [hrN,hfN,hsM]

/-- A purely analytic coefficient payment, independent of the sixth value and
of any old whole-mother counting lower bound. -/
theorem coefficient_payment (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      4*Q c-ε ≤ FullLogMother.psiCoefficient δ+c-FullSourceLog.GammaLog6+
        8*L-8*I-ε/3 := by
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
  refine ⟨δ,hδ,hδhi,?_⟩
  rw [FullLogCount.fixed_same_mother_identity]
  unfold Q LogP2.Qlog Phase20.unroundedCoefficient
  linarith only [hcoef,hh,hbudget]

/-- A reusable single-slot composer; all other actual producers are closed in
SixthSlotCore, and division by four occurs only at this endpoint. -/
theorem ordinary_P2 {c : ℝ} (h6 : SixthLower c) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Q c-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδhi,hcoef⟩ := coefficient_payment c (show 0 < 4*η by positivity)
  obtain ⟨T,hT,hcount⟩ := ordinary_replacement h6 hδ hδhi (show 0 < (4*η)/3 by positivity)
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hc := hcount N hN he
  have hs : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  have hm := (mul_le_mul_of_nonneg_right hcoef hs).trans hc
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hm
  have hid : (Q c-η)*U8CanonicalMother.M N =
      ((4*Q c-4*η)*U8CanonicalMother.M N)/4 := by ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hm])

end
end SixthSlotAssembly
