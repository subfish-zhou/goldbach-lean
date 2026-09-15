import U8MotherSmallResidual
import U8OriginalSmallIntegral
import U8SymbolicSmallGain

/-! Actual same-mother consumption in the canonical carrier environment.
The unrestricted ordinary-P2 count is not identified with a refined good count. -/
noncomputable section
open Finset Real
open scoped Interval
open Wu2008DoubleSieve
namespace U8CanonicalMother

abbrev L : ℝ := OriginalU8.SymbolicSmallGain.L
abbrev I : ℝ := OriginalU8.Weighted.originalSmallIntegral

def M (N : ℕ) : ℝ := wuSingularSeries N * N / log N ^ (2 : ℕ)

theorem small_eq_physicalSmall (N : ℕ) :
    U8MotherInsertion.small N = U8Literal.physicalSmall N := rfl

theorem scale_eq_liu {N : ℕ} (hN : 0 < N) :
    M N = MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * N /
      log N ^ (2 : ℕ) := U8MotherInsertion.original_normalization hN

theorem L_eq_oldSmallIntegral : L = U8MotherInsertion.oldSmallIntegral := rfl

theorem L_literal : L = ∫ t in (100/1327 : ℝ)..(1/10),
    log (2-3*t)/(t*(1-t)) := OriginalU8.SymbolicSmallGain.L_literal

theorem I_literal : I = (9/10 : ℝ) * ∫ t in (100/1327 : ℝ)..(1/10),
    log (2-3*t)/(t*(1-t)^2) := OriginalU8.SymbolicSmallGain.I_literal

/-- Both real producers choose their thresholds before the common even N. -/
theorem ordinary_replacement {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullAdmissibleMother.psiCoefficient δ + 8*L - 8*I - ε) * M N ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨Tm,hTm,hm⟩ := U8MotherInsertion.ordinary_small_debit hδ hδhi (half_pos hε)
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/2) (half_pos hε)
  refine ⟨max Tm Ts,hTm.trans (le_max_left _ _),?_⟩
  intro N hN heven
  have hmN := hm N ((le_max_left _ _).trans hN) heven
  have hsN := hs N ((le_max_right _ _).trans hN) heven
  have h512 : 512 ≤ N := hTm.trans ((le_max_left _ _).trans hN)
  have hnorm := scale_eq_liu (show 0 < N by omega)
  rw [← small_eq_physicalSmall] at hsN
  rw [← L_eq_oldSmallIntegral] at hmN
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤ (8*I+ε/2)*M N := by
    rw [hnorm]
    convert hsN using 1
    ring
  have hmM : (FullAdmissibleMother.psiCoefficient δ+8*L-ε/2)*M N -
      ((U8MotherInsertion.small N).card : ℝ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    convert hmN using 1
    dsimp [M]
    ring
  nlinarith only [hmM,hsM]

open SingleUpperHIntegral HighSixDeltaLimit

/-- The sixth correction is already included in this Q; it is not paid again. -/
def Q : ℝ := FullAdmissibleCount.unroundedCoefficient

def improvedCoefficient : ℝ := Q + 2*(L-I)

/-- Delta is chosen directly from the coefficient limit, not from an old lower bound. -/
theorem same_mother_delta_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (limitCoefficient+4*Phase18.g18+
          (8*BaseHGain.originalGain+fifthHGain+(FullAdmissibleSeed.Gamma6-47/481250))+
          8*L-8*I-ε)*M N ≤
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
      (8*BaseHGain.originalGain+fifthHGain+(FullAdmissibleSeed.Gamma6-47/481250))+
      8*L-8*I-ε ≤ FullAdmissibleMother.psiCoefficient δ+8*L-8*I-ε/3 := by
    rw [FullAdmissibleCount.fixed_same_mother_identity]
    linarith only [hcoef,hh,hbudget]
  have hs : 0 ≤ M N := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right hc hs).trans hm

/-- Divide by four exactly once, with no old ordinary lower used. -/
theorem improved_ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (improvedCoefficient-η)*M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := same_mother_delta_payment (show 0 < 4*η by positivity)
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hn
  have hid : (improvedCoefficient-η)*M N =
      ((limitCoefficient+4*Phase18.g18+
        (8*BaseHGain.originalGain+fifthHGain+(FullAdmissibleSeed.Gamma6-47/481250))+
        8*L-8*I-4*η)*M N)/4 := by
    unfold improvedCoefficient Q FullAdmissibleCount.unroundedCoefficient Phase20.unroundedCoefficient
    ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])

/-- The previously frozen positive rational certificate is actually consumed. -/
theorem improved_gain_certificate :
    (70/17 : ℝ)*((1/10 : ℝ)-(100/1327))^2 ≤ improvedCoefficient-Q ∧
      0 < improvedCoefficient-Q := by
  have h := OriginalU8.SymbolicSmallGain.literal_gain_certificate
  have hl : (70/17 : ℝ)*((1/10 : ℝ)-(100/1327))^2 ≤ 2*(L-I) := h.2.1
  have hp : 0 < 2*(L-I) := h.2.2
  exact ⟨by dsimp [improvedCoefficient]; linarith only [hl],
    by dsimp [improvedCoefficient]; linarith only [hp]⟩

/-- A literal positive rational gain on the same unrestricted ordinary count. -/
theorem rational_gain_ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Q+(70/17 : ℝ)*((1/10 : ℝ)-(100/1327))^2-η)*M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := improved_ordinary_P2 η hη
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hc : Q+(70/17 : ℝ)*((1/10 : ℝ)-(100/1327))^2-η ≤ improvedCoefficient-η := by
    linarith only [improved_gain_certificate.1]
  have hs : 0 ≤ M N := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right hc hs).trans (h N hN he)

end U8CanonicalMother
