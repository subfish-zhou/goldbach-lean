import PositiveCoreFullCross

namespace PositiveSecondPayment
open Wu2008DoubleSieve Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open Wu2008DoubleSieve.BaseLowerCounts
noncomputable section

/-- The unchanged original F2 exponent and the full-cross denominator. -/
def secondGain : ℝ := (11/2-(1/(2*(25/206 : ℝ))))^3/70875

theorem secondGain_pos : 0 < secondGain := by norm_num [secondGain]

/-- Strict fixed rational algebra; no new parameter selection or numerical search. -/
theorem secondGain_strict : BaseHGain.originalGain < secondGain := by
  norm_num [BaseHGain.originalGain, secondGain]

/-- Uniform payment at the original moving sieve argument. -/
theorem second_h_uniform {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    secondGain ≤ wuImprovementLimit false δ ((1/2-δ)/(25/206)) := by
  have hs : (4 : ℝ) ≤ (1/2-δ)/(25/206) := by norm_num; linarith
  have ht : (1/2-δ)/(25/206) ≤ (11/2 : ℝ) := by norm_num; linarith
  have hl := PositiveCoreResume.h_full_cross hδ hδhi hs ht
  have hp : (11/2-(1/(2*(25/206 : ℝ))))^3 ≤
      (11/2-(1/2-δ)/(25/206))^3 := by
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
    linarith
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans hl

/-- Rebuild F2 from the raw fixed-delta source, including the nonpositive branch
and the original logarithmic-integral normalization and inverse-N payment. -/
theorem second_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^(25/206 : ℝ)) : ℝ) := by
  by_cases hzero : (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε ≤ 0
  · refine ⟨4, le_rfl, ?_⟩
    intro N hN _he
    have hs : 0 ≤ wuSingularSeries N * N / log N^(2 : ℕ) :=
      truncatedSixthClosure_scale_nonneg hN
    have h := mul_nonpos_of_nonpos_of_nonneg hzero hs
    have hn : (0 : ℝ) ≤ sieveCount N 1 N ((N : ℝ)^(25/206 : ℝ)) := by
      unfold sieveCount
      positivity
    have h' : ((8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤ 0 := by
      simpa only [mul_div_assoc, mul_assoc] using h
    exact h'.trans hn
  · have htarget : 0 < (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε := lt_of_not_ge hzero
    obtain ⟨δ, η, hδ, hδhi, hη, hs, hs10, hclose⟩ := choose_parameters (κ := (25/206 : ℝ)) (by norm_num) (by norm_num) hε
    have hc : 0 < (1/2 : ℝ)-δ := by linarith
    have hh := second_h_uniform hδ hδhi
    change secondGain ≤ wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ)) at hh
    have hg : 8*secondGain ≤ 4*wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ))/(1/2-δ) := by
      apply (le_div_iff₀ hc).mpr
      have hp := secondGain_pos
      nlinarith
    have hclose : (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε/2 <
        4*(wuLowerCoefficient ((1/2-δ)/(25/206 : ℝ))+
          wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ))-η)/(1/2-δ) := by
      have he : 4*(wuLowerCoefficient ((1/2-δ)/(25/206 : ℝ))+
          wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ))-η)/(1/2-δ) =
          4*(wuLowerCoefficient ((1/2-δ)/(25/206 : ℝ))-η)/(1/2-δ)+
          4*wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ))/(1/2-δ) := by ring
      rw [he]
      linarith
    let b := wuLowerCoefficient ((1/2-δ)/(25/206 : ℝ))+
      wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ))-η
    let B := 4*b/(1/2-δ)
    have hB : 0 < B := by dsimp [B, b]; linarith
    have hb : 0 ≤ b := by
      have h := (lt_div_iff₀ hc).mp hB
      nlinarith
    obtain ⟨T, hT4, hT⟩ := fixed_delta_li_with_h hδ (by linarith) hs hs10 hη
    obtain ⟨M, hM⟩ := exists_nat_ge (4*B/ε)
    refine ⟨max T M, hT4.trans (le_max_left _ _), ?_⟩
    intro N hN he
    have hNT : T ≤ N := (le_max_left _ _).trans hN
    have hN4 : 4 ≤ N := hT4.trans hNT
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hMN : (M : ℝ) ≤ N := by exact_mod_cast ((le_max_right T M).trans hN)
    have hbudget : 4*B ≤ (N : ℝ)*ε := (div_le_iff₀ hε).mp (hM.trans hMN)
    have hsmall : B*(2/(N : ℝ)) ≤ ε/2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNr).mpr
      nlinarith
    have hcoef : (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε ≤ B*(1-2/(N : ℝ)) := by
      change (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε/2 < B at hclose
      nlinarith
    have hscale : 0 ≤ wuSingularSeries N * N / log N^(2 : ℕ) :=
      truncatedSixthClosure_scale_nonneg hN4
    have hmain := mul_le_mul_of_nonneg_right hcoef hscale
    have hmain' : ((8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*secondGain)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        B*(1-2/(N : ℝ))*wuSingularSeries N*N/log N^(2 : ℕ) := by
      simpa only [mul_div_assoc, mul_assoc] using hmain
    exact hmain'.trans ((normalized_li_lower hN4 hc hb).trans (hT N hNT he))

end
end PositiveSecondPayment
