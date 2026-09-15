import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleShiftedBoundary
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassTheta

namespace Wu2008DoubleSieve.LowerTripleGroupedBoundary
open Finset Real LowerTripleGroupedFinite
open scoped Classical

/-- The entire varying density coefficient stays on both actual finite mains.
Only the shifted boundary is paid; neither unit terms nor PNT errors occur. -/
theorem finiteMain_six_boundary_density_paid (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible → 2 ≤ P.s →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 6, finiteBuchstabMain N δ Δ V P j * A ≤
        unshiftedFiniteBuchstabMain N δ Δ V P j * A + ε*Θ) ∧
      (∑ j : Fin 6, finiteBuchstabMain N δ Δ V P j) * A ≤
        (∑ j : Fin 6, unshiftedFiniteBuchstabMain N δ Δ V P j) * A + ε*Θ := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith)
    (by positivity)) (div_pos (by norm_num) (by linarith))
  obtain ⟨T,hT,hraw⟩ := finiteMain_six_boundary_paid k hδ hδhi
    (div_pos (show 0 < 2*ε by positivity) hA)
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb P hp hs
  have hN4 := hT.trans hN
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hh := hraw N hN i Δ V hb P hp hs
  have hpay := mul_le_mul_of_nonneg_left
    (HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb)
    (show 0 ≤ 2*ε by positivity)
  have hcancel : (2*ε/A) * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) *
      (A * (wuSingularSeries N/log N)) =
      (2*ε) * (wuSingularSeries N/log N * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by field_simp
  have join (x y : ℝ) (hxy : x ≤ y + (2*ε/A)*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :
      x * (A*wuSingularSeries N/log N) ≤ y * (A*wuSingularSeries N/log N) +
        ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    have h := mul_le_mul_of_nonneg_right hxy (mul_nonneg hA.le hC)
    rw [add_mul, hcancel] at h
    rw [mul_div_assoc]
    linarith
  exact ⟨fun j => join _ _ (hh.1 j), join _ _ hh.2⟩

end Wu2008DoubleSieve.LowerTripleGroupedBoundary
