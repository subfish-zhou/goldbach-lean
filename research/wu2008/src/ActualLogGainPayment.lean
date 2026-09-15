import HighOriginalMother

namespace ActualLogGain
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Any logarithmic remainder is paid uniformly on the actual original Fin2 boxes.
The lower mass and its strict positivity are constructed, not assumed. -/
theorem original_remainder_relative {δ ε : ℝ} (C : ℝ)
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      C*N/log (N : ℝ)^(18 : ℝ) ≤
        ε*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨T1,hmass⟩ := wu_boxConvolution_mass_bounds 3 hη
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  let c : ℝ := 2*liuUniversalProduct*(1/12 : ℝ)^3
  have hc : 0 < c := by dsimp [c]; have := liuUniversalProduct_pos; positivity
  obtain ⟨T3,hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 1 (C/(ε*c)))))
  refine ⟨max 4 (max T1 (max T2 T3)),le_max_left _ _,?_⟩
  intro N hN Δ hlo hhi V hV hr
  have hN4 : 4 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN3 : T3 ≤ N := by omega
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr
  have hend := original_endpoints (show 2 ≤ N by omega) hV hr
  have hlog : 0 < log (N : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans (hlogBudget N hN3))
  have htheta : c*N/log N^17 ≤ boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    have hm := (hmass N hN1 2 (by norm_num) Δ hlo hhi V hend.1 hend.2).1
    have hw := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 2*liuUniversalProduct*N/log N^2 by have := liuUniversalProduct_pos; positivity)
    have ht := theta_from_actual_support _ hN4 hδ.le hη (fun j p hp => (hg.1 j p hp).1) hg.2
    calc
      _ = 2*liuUniversalProduct*N/log N^2*((1/12 : ℝ)^3/log N^(5*3)) := by dsimp [c]; ring
      _ ≤ _ := hw.trans ht
  have hb : C/log N ≤ ε*c := by
    apply (div_le_iff₀ hlog).mpr
    have hh := (div_le_iff₀ (show 0 < ε*c by positivity)).mp
      ((le_max_right _ _).trans (hlogBudget N hN3))
    dsimp only [Function.comp_apply] at hh
    nlinarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨(by positivity : 0 < c*N/log N^17).trans_le htheta,?_⟩
  calc
    _ = (C/log N)*((N : ℝ)/log N^17) := by norm_num; ring
    _ ≤ (ε*c)*((N : ℝ)/log N^17) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = ε*(c*N/log N^17) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

end
end ActualLogGain
