import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeRelative

namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Real Filter Finset
open scoped Classical Topology

/-- Relative payment for an arbitrary original-weight physical family.
This is a generic implication: actual producers must supply the power gap,
positive weights and full weighted cofactor-fibre bound. No unit equation,
inhabitance assumption, modulus-dependent layers or altered AP center is used. -/
theorem R1_theta_relative (k : ℕ) {δ ε η F : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε)
    (hη : 0 < η) (hF : 0 ≤ F) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ (N : ℕ), T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ (α : Type*) (L : Family α N),
      (∀ c ∈ L.labels, (N:ℝ)^η ≤ L.cofactor c ∧
        (L.cofactor c : ℝ) ≤ (N:ℝ)^(1-η)) →
      (∀ c ∈ L.labels, 1 ≤ L.weight c) →
      (∀ e, (∑ c ∈ L.layerFibre e, L.weight c) ≤ F) → ∀ Z : ℝ,
      L.R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T1, hT1, hd⟩ := R1_log_saving (5*k+3 : ℕ) η F
    (by positivity) hη hF hδ
  obtain ⟨c, hc, T2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  obtain ⟨T3, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C/(ε*c))))
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb α L hp hw hf Z
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hlog := log_pos (by exact_mod_cast
    (show 1 < N by have := hT1.trans hN1; omega) : (1:ℝ) < N)
  have hr := hd N hN1 α L hp hw hf Z
  rw [rpow_natCast] at hr
  have htheta := hTheta N hN2 i hb.1 Δ hb.2.1 hb.2.2.1 V
    hb.2.2.2.2.1 hb.2.2.2.2.2
  have hbudget : C / log (N:ℝ) ≤ ε*c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp (hlogT N hN3)
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C*N / log (N:ℝ)^(5*k+3) := hr
    _ = (C/log (N:ℝ))*((N:ℝ)/log (N:ℝ)^(5*k+2)) := by
      rw [show 5*k+3 = (5*k+2)+1 by omega, pow_succ]
      ring
    _ ≤ (ε*c)*((N:ℝ)/log (N:ℝ)^(5*k+2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε*(c*(N:ℝ)/log (N:ℝ)^(5*k+2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

/-- One threshold and one total epsilon for two possibly different label types. -/
theorem R1_pair_theta_relative (k : ℕ) {δ ε η F : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε)
    (hη : 0 < η) (hF : 0 ≤ F) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ (N : ℕ), T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ (α β : Type*) (L : Family α N) (M : Family β N),
      (∀ c ∈ L.labels, (N:ℝ)^η ≤ L.cofactor c ∧
        (L.cofactor c:ℝ) ≤ (N:ℝ)^(1-η)) →
      (∀ c ∈ M.labels, (N:ℝ)^η ≤ M.cofactor c ∧
        (M.cofactor c:ℝ) ≤ (N:ℝ)^(1-η)) →
      (∀ c ∈ L.labels, 1 ≤ L.weight c) →
      (∀ c ∈ M.labels, 1 ≤ M.weight c) →
      (∀ e, (∑ c ∈ L.layerFibre e, L.weight c) ≤ F) →
      (∀ e, (∑ c ∈ M.layerFibre e, M.weight c) ≤ F) → ∀ Z : ℝ,
      L.R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z + M.R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1,hT1,hd1⟩ := R1_theta_relative k hδ hδhi (show 0 < ε/2 by positivity) hη hF
  obtain ⟨T2,_,hd2⟩ := R1_theta_relative k hδ hδhi (show 0 < ε/2 by positivity) hη hF
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb α β L M hpL hpM hwL hwM hfL hfM Z
  have hL := hd1 N ((le_max_left _ _).trans hN) i Δ V hb α L hpL hwL hfL Z
  have hM := hd2 N ((le_max_right _ _).trans hN) i Δ V hb β M hpM hwM hfM Z
  linarith

end Wu2008DoubleSieve.LabelledPhysical.Family
