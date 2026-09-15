import ParentPhase9HalfWeight
import MathlibNt.Wu2008DoubleSieve.HighSixLowHActualCount
import MathlibNt.Wu2008DoubleSieve.HighSixPhase6ExactCount

namespace Wu2008DoubleSieve.ParentPhase9HalfWeightCount
open Real SingleUpperHIntegral HighSixDeltaLimit ParentPhase9HalfWeight
noncomputable section

/-- This is an identity between the same signed mother expressions, not a sum of counts. -/
theorem same_mother_identity (δ : ℝ) :
    HighSixLowHMother.psiCoefficient δ = HighSixPsiMother.psiCoefficient δ + gainH34 δ := by
  unfold HighSixLowHMother.psiCoefficient HighSixPsiMother.psiCoefficient
  ring

/-- The uniform H bound is combined with the original Psi/Gdelta approximation.
The positive delta is selected before the common arithmetic threshold. -/
theorem actual_count_delta_then_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (limitCoefficient+4*gainConstant-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,ha1,hclose⟩ := coefficient_close he
  let L : ℝ := (100/49)*penaltyCost
  have hL : 0 < L := mul_pos (by norm_num) penaltyCost_pos
  let δ : ℝ := min (a/2) (ε/(12*(L+1)))
  have hδ : 0 < δ := lt_min (half_pos ha) (div_pos hε (by positivity))
  have hδa : δ < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hδhi : δ ≤ 1/100 := hδa.le.trans ha1
  have hδb : δ ≤ ε/(12*(L+1)) := min_le_right _ _
  have hpay : 12*(L+1)*δ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(L+1))).mp hδb
    nlinarith only [hh]
  have hbudget : 4*L*δ ≤ ε/3 := by nlinarith only [hpay,hδ]
  have hcoef := (abs_lt.mp (hclose δ hδ hδa)).1
  have hH := gain_lower_linear_error hδ hδhi
  change gainConstant-L*δ ≤ gainH34 δ/4 at hH
  obtain ⟨T,hT,hcount⟩ := HighSixLowHMother.actual_count_lower hδ hδhi he
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN heven
  have hm := hcount N hN heven
  rw [same_mother_identity] at hm
  have hc : limitCoefficient+4*gainConstant-ε ≤
      HighSixPsiMother.psiCoefficient δ+gainH34 δ-ε/3 := by
    linarith only [hcoef,hH,hbudget]
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hp := mul_le_mul_of_nonneg_right hc hs
  calc
    _ = (limitCoefficient+4*gainConstant-ε)*(wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ (HighSixPsiMother.psiCoefficient δ+gainH34 δ-ε/3)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
    _ = (HighSixPsiMother.psiCoefficient δ+gainH34 δ-ε/3)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := hm

/-- The strict reserve of the same complete K pays the approximation error.
Only the phase4 joined H+Psi count theorem supplies a counting estimate. -/
theorem curvature_with_H_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gainConstant)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have he : 0 < limitCoefficient-(GCurvatureChord.newBalance+localGainOne) :=
    sub_pos.mpr HighSixDeltaLimit.curvature_coefficient_strict
  obtain ⟨δ,_,_,T,hT,h⟩ := actual_count_delta_then_threshold he
  refine ⟨T,hT,?_⟩
  intro N hN heven
  have hn := h N hN heven
  have hid : limitCoefficient+4*gainConstant-
      (limitCoefficient-(GCurvatureChord.newBalance+localGainOne)) =
      GCurvatureChord.newBalance+localGainOne+4*gainConstant := by ring
  rw [hid] at hn
  have hq : (GCurvatureChord.newBalance/4+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gainConstant)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    have heq : (GCurvatureChord.newBalance/4+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gainConstant)*
        wuSingularSeries N*N/log N^(2 : ℕ) =
        ((GCurvatureChord.newBalance+localGainOne+4*gainConstant)*
          wuSingularSeries N*N/log N^(2 : ℕ))/4 := by
      unfold localGainOne
      ring
    rw [heq]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])
  rwa [GCurvatureChord.quarter_eq_exact] at hq

/-- Strictly stronger than the phase6 rational coefficient. -/
theorem rational_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ) <
      GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+gainConstant := by
  linarith only [gainConstant_pos]

/-- The literal ordinary P2 carrier: complement one is retained and zero excluded.
The threshold is shared by source notation and the fully expanded filter. -/
theorem exact_gain_actual_count_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+
          (224077077822547266182001/786669346455967990704800000 : ℝ))*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+
          (224077077822547266182001/786669346455967990704800000 : ℝ))*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := curvature_with_H_actual_count
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hcoef : GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+gainConstant ≤
      GCurvatureChord.exactQuarter+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gainConstant := by
    linarith only [HighSixPhase6.exact_local_gain_lower]
  have hp := mul_le_mul_of_nonneg_right hcoef hs
  have hn := h N hN he
  have hc : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+gainConstant)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ)+gainConstant)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gainConstant)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gainConstant)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn
  rw [gainConstant_eq] at hc
  exact ⟨hc,hc⟩

end
end Wu2008DoubleSieve.ParentPhase9HalfWeightCount
