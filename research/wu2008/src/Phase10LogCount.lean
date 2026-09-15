import Phase10LogFeedback
import ParentPhase9HalfWeightCount

namespace Wu2008DoubleSieve.Phase10
open Real SingleUpperHIntegral HighSixDeltaLimit
noncomputable section

/-- Reusable payment at the same H+Psi mother. The hypothesis concerns the raw H integral,
not a count estimate. Delta precedes the one common arithmetic threshold. -/
theorem same_mother_delta_payment (g error : ℝ) (herror : 0 < error)
    (hH : ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → g-error*δ ≤ gainH34 δ/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (limitCoefficient+4*g-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,ha1,hclose⟩ := coefficient_close he
  let δ : ℝ := min (a/2) (ε/(12*(error+1)))
  have hδ : 0 < δ := lt_min (half_pos ha) (div_pos hε (by positivity))
  have hδa : δ < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hδhi : δ ≤ 1/100 := hδa.le.trans ha1
  have hδb : δ ≤ ε/(12*(error+1)) := min_le_right _ _
  have hpay : 12*(error+1)*δ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(error+1))).mp hδb
    nlinarith only [hh]
  have hbudget : 4*error*δ ≤ ε/3 := by nlinarith only [hpay,hδ]
  have hcoef := (abs_lt.mp (hclose δ hδ hδa)).1
  have hh := hH δ hδ hδhi
  obtain ⟨T,hT,hcount⟩ := HighSixLowHMother.actual_count_lower hδ hδhi he
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN heven
  have hm := hcount N hN heven
  rw [ParentPhase9HalfWeightCount.same_mother_identity] at hm
  have hc : limitCoefficient+4*g-ε ≤
      HighSixPsiMother.psiCoefficient δ+gainH34 δ-ε/3 := by
    linarith only [hcoef,hh,hbudget]
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hp := mul_le_mul_of_nonneg_right hc hs
  calc
    _ = (limitCoefficient+4*g-ε)*(wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ (HighSixPsiMother.psiCoefficient δ+gainH34 δ-ε/3)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
    _ = (HighSixPsiMother.psiCoefficient δ+gainH34 δ-ε/3)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := hm

/-- The same complete K supplies the strict reserve, with a generic raw H producer. -/
theorem same_mother_exact_payment (g error : ℝ) (herror : 0 < error)
    (hH : ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → g-error*δ ≤ gainH34 δ/4) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have he : 0 < limitCoefficient-(GCurvatureChord.newBalance+localGainOne) :=
    sub_pos.mpr HighSixDeltaLimit.curvature_coefficient_strict
  obtain ⟨δ,_,_,T,hT,h⟩ := same_mother_delta_payment g error herror hH he
  refine ⟨T,hT,?_⟩
  intro N hN heven
  have hn := h N hN heven
  rw [← GCurvatureChord.quarter_eq_exact]
  have heq : (GCurvatureChord.newBalance/4+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g)*
      wuSingularSeries N*N/log N^(2 : ℕ) =
      ((limitCoefficient+4*g-(limitCoefficient-(GCurvatureChord.newBalance+localGainOne)))*
        wuSingularSeries N*N/log N^(2 : ℕ))/4 := by
    unfold localGainOne
    ring
  rw [heq]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])

/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem log_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gLog)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  same_mother_exact_payment gLog ((100/49)*penaltyLog)
    (mul_pos (by norm_num) penaltyLog_pos)
    (fun _ hδ hδhi => gain_log_linear_error hδ hδhi)

/-- Ordinary P2 includes complement one and excludes zero; no prime-factor ratio filter.
Both spellings share the same threshold. -/
theorem log_ordinary_P2_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+gLog)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+gLog)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := log_actual_count
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hc : GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+gLog ≤
      GCurvatureChord.exactQuarter+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gLog := by
    linarith only [HighSixPhase6.exact_local_gain_lower]
  have hp := mul_le_mul_of_nonneg_right hc hs
  have hn := h N hN he
  have hfinal : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+gLog)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ)+gLog)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gLog)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+gLog)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn
  exact ⟨hfinal,hfinal⟩

theorem ordinary_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+
      ParentPhase9HalfWeight.gainConstant <
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+gLog := by
  linarith only [gLog_strict]

end
end Wu2008DoubleSieve.Phase10
