import InsertedO2Mother
import ActualLogGainFinal

namespace InsertedGain
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- A common mass/remainder kernel for at most three actual coordinate windows.
No original-rectangle or insertion-specific hypothesis is hidden in the proof. -/
theorem supported_remainder_relative {δ η ε : ℝ} (C : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ i : ℕ, i ≤ 3 → ∀ V : Fin i → ℝ,
      (∀ j, (N : ℝ)^η ≤ V j) → (∀ j, V j ≤ N) →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      C*N/log (N : ℝ)^(18 : ℝ) ≤
        ε*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hmass⟩ := wu_boxConvolution_mass_bounds 3 hη
  let c : ℝ := 2*liuUniversalProduct*(1/12 : ℝ)^3
  have hc : 0 < c := by dsimp [c]; have := liuUniversalProduct_pos; positivity
  obtain ⟨T1,hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 1 (C/(ε*c)))))
  refine ⟨max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN Δ hlo hhi i hi V hV hVN hW hsize
  have hN4 : 4 ≤ N := by omega
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hlog : 0 < log (N : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans (hlogBudget N hN1))
  have hm := (hmass N hN0 i hi Δ hlo hhi V hV hVN).1
  have hw := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ 2*liuUniversalProduct*N/log N^2 by have := liuUniversalProduct_pos; positivity)
  have ht := theta_from_actual_support _ hN4 hδ hη hW hsize
  have htheta : c*N/log N^17 ≤ boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    calc
      _ = 2*liuUniversalProduct*N/log N^2*((1/12 : ℝ)^3/log N^(5*3)) := by dsimp [c]; ring
      _ ≤ _ := hw.trans ht
  have hb : C/log N ≤ ε*c := by
    apply (div_le_iff₀ hlog).mpr
    have hh := (div_le_iff₀ (show 0 < ε*c by positivity)).mp
      ((le_max_right _ _).trans (hlogBudget N hN1))
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
end InsertedGain
