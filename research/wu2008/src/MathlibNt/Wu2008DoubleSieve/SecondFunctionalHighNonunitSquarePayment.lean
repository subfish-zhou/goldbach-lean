import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledSquareCofactor
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorInputs

/-! Both original source families pay their large-square raw pieces from one
relative epsilon budget. No prime-exception mass bound is used. -/
namespace Wu2008DoubleSieve.HighNonunit
open Finset Real Filter
open scoped Classical

/-- A uniform actual-source payment, preserving all original weights and raw fibres.
The threshold is chosen before N, every source box and every mother parameter. -/
theorem source_squareRawMass_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let Y := (N : ℝ)^(wuLocalExponent k δ / 10)
      (sourceFamily N δ Δ V p false).squareRawMass Y +
        (sourceFamily N δ Δ V p true).squareRawMass Y ≤
          ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+5)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hH : 1 ≤ H := le_max_left _ _
  have hF : 0 < F := pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  obtain ⟨T0,hT04,hT0⟩ := source_error_inputs k hδ hδhi
  obtain ⟨T1,_,hT1⟩ := omega3_absolute_power_log_relative k 1 hδ hδhi hε
    (show 0 < 8*F by positivity) hη
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 0 (show (0 : ℝ) < 2 by norm_num) hη)
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3,hT3⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  let T := max T0 (max T1 (max T2 T3))
  refine ⟨T,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  have hN0 : T0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : T3 ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let Y := (N : ℝ)^η
  have hY : 2 ≤ Y := by simpa only [pow_zero, mul_one] using hT2 N hN2
  have hY0 : 0 < Y := by linarith
  have hYm : 0 < Y-1 := by linarith
  have hlog1 := hT3 N hN3
  have hin := hT0 N hN0 i Δ V hb p hp
  have hf (high : Bool) : ∀ e,
      (∑ x ∈ (sourceFamily N δ Δ V p high).labels.filter
        (fun x => (sourceFamily N δ Δ V p high).cofactor x = e),
          (sourceFamily N δ Δ V p high).weight x) ≤ F := by
    exact (hin.1 high false).2
  have h0 := (sourceFamily N δ Δ V p false).squareRawMass_le hY hF.le (hf false)
  have h1 := (sourceFamily N δ Δ V p true).squareRawMass_le hY hF.le (hf true)
  have hd : 1/(Y-1) ≤ 2/Y := by
    apply (div_le_div_iff₀ hYm hY0).mpr
    linarith
  change (sourceFamily N δ Δ V p false).squareRawMass Y +
    (sourceFamily N δ Δ V p true).squareRawMass Y ≤ _
  calc
    _ ≤ 2*F*N*(1+log N)/(Y-1) :=
      (add_le_add h0 h1).trans_eq (by ring)
    _ = (2*F*N*(1+log N))*(1/(Y-1)) := by ring
    _ ≤ (2*F*N*(1+log N))*(2/Y) := by
      apply mul_le_mul_of_nonneg_left hd
      have : 0 ≤ log (N : ℝ) := by linarith
      positivity
    _ ≤ (2*F*N*(2*log N))*(2/Y) := by
      gcongr
      linarith
    _ = (8*F)*N*log N^1/(N : ℝ)^η := by dsimp only [Y]; ring
    _ ≤ _ := hT1 N hN1 i Δ V hb

end Wu2008DoubleSieve.HighNonunit
