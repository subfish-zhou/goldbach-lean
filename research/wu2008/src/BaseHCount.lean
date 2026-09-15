import BaseHCross

namespace Wu2008DoubleSieve.BaseHGain
open Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open BaseLowerCounts

/-- A paper-derived uniform gain, without numerical evaluation or parameter search. -/
noncomputable def originalGain : ℝ := (11/2-(1/(2*(25/206 : ℝ))))^3/378000

theorem originalGain_pos : 0 < originalGain := by norm_num [originalGain]

/-- The actual original F2 count, with the new gain paid through the same raw source. -/
theorem original_F2_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^(25/206 : ℝ)) : ℝ) := by
  by_cases hzero : (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε ≤ 0
  · refine ⟨4, le_rfl, ?_⟩
    intro N hN _he
    have hs : 0 ≤ wuSingularSeries N * N / log N^(2 : ℕ) :=
      truncatedSixthClosure_scale_nonneg hN
    have h := mul_nonpos_of_nonpos_of_nonneg hzero hs
    have hn : (0 : ℝ) ≤ sieveCount N 1 N ((N : ℝ)^(25/206 : ℝ)) := by
      unfold sieveCount
      positivity
    have h' : ((8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤ 0 := by
      simpa only [mul_div_assoc, mul_assoc] using h
    exact h'.trans hn
  · have htarget : 0 < (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε := lt_of_not_ge hzero
    obtain ⟨δ, η, hδ, hδhi, hη, hs, hs10, hclose⟩ := choose_parameters (κ := (25/206 : ℝ)) (by norm_num) (by norm_num) hε
    have hc : 0 < (1/2 : ℝ)-δ := by linarith
    have hh := original_F2_h hδ hδhi
    change originalGain ≤ wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ)) at hh
    have hg : 8*originalGain ≤ 4*wuImprovementLimit false δ ((1/2-δ)/(25/206 : ℝ))/(1/2-δ) := by
      apply (le_div_iff₀ hc).mpr
      have hp := originalGain_pos
      nlinarith
    have hclose : (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε/2 <
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
    have hcoef : (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε ≤ B*(1-2/(N : ℝ)) := by
      change (8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε/2 < B at hclose
      nlinarith
    have hscale : 0 ≤ wuSingularSeries N * N / log N^(2 : ℕ) :=
      truncatedSixthClosure_scale_nonneg hN4
    have hmain := mul_le_mul_of_nonneg_right hcoef hscale
    have hmain' : ((8*wuLowerCoefficient (1/(2*(25/206 : ℝ)))+8*originalGain)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        B*(1-2/(N : ℝ))*wuSingularSeries N*N/log N^(2 : ℕ) := by
      simpa only [mul_div_assoc, mul_assoc] using hmain
    exact hmain'.trans ((normalized_li_lower hN4 hc hb).trans (hT N hNT he))


end Wu2008DoubleSieve.BaseHGain
