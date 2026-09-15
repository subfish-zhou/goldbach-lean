import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSourceKMasses
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassTheta

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighNonunit
open Finset Real Filter HighNonunitLegal
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- A common threshold precedes every source box, mother parameter, and supported d.
Both complete words retain the very same actual source phi. -/
theorem sourceClosedK_pair_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        |(sourceClosedK N d δ p false + sourceClosedK N d δ p true) -
          (sourceLegalK N d δ p false + sourceLegalK N d δ p true)| < epsilon := by
  let Phi := max 2 (1 / wuLocalExponent k δ)
  obtain ⟨R0, _, hR0⟩ := closedPrimeK_pair_uniform Phi (le_max_left _ _) epsilon he
  have heta := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb p hp hs d hd
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hgap : 0 < 2 * δ / (1/2-δ) := by positivity
    linarith [hg.2.2.1]
  obtain ⟨ha, h23, _, hbhi⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  simpa only [sourceClosedK, sourceLegalK, Bool.false_eq_true, if_false, if_true] using
    hR0 _ hlarge _ ⟨hphi, hg.2.2.2.trans (le_max_right _ _)⟩
      _ _ _ ha h23 hbhi

/-- The quadrature discrepancy is paid on the original coefficient reciprocal mass.
No coefficient, source phi, or zero-mass case is cancelled. -/
theorem sourceClosedKMass_pair_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        |(sourceClosedKMass N δ Δ V p false + sourceClosedKMass N δ Δ V p true) -
          (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true)| ≤
        epsilon * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have heta := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT4, hT⟩ := sourceClosedK_pair_uniform k hδ hδhi (mul_pos he heta)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have hN2 : 2 ≤ N := by omega
  let W := convolutionWuWindows N Δ V
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ) *
    ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d))
  let E := fun d => (sourceClosedK N d δ p false + sourceClosedK N d δ p true) -
    (sourceLegalK N d δ p false + sourceLegalK N d δ p true)
  have hid : (sourceClosedKMass N δ Δ V p false + sourceClosedKMass N δ Δ V p true) -
      (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true) =
      ∑ d ∈ boxConvolutionSupport W, w d * E d := by
    unfold sourceClosedKMass sourceLegalKMass
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    dsimp only [w, E, W]
    ring
  rw [hid]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d * E d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W,
        epsilon * ((N:ℝ)/log N) * ((convolutionCoeff W d : ℝ)/d) := by
      apply sum_le_sum
      intro d hd
      have hg := omega3XPhi_source_bounds hN2 hδ hδhi hb hd
      have hlog := log_pos hg.2.1
      have hw : 0 ≤ w d := by dsimp only [w]; positivity
      have hE : |E d| ≤ epsilon * wuLocalExponent k δ :=
        (hT N hN i Δ V hb p hp hs d hd).le
      have hscale := omega3X_log_scale_error_le hN2 hδ hδhi hb hd he.le
      calc
        _ = w d * |E d| := by rw [abs_mul, abs_of_nonneg hw]
        _ ≤ w d * (epsilon * wuLocalExponent k δ) :=
          mul_le_mul_of_nonneg_left hE hw
        _ = (convolutionCoeff W d : ℝ) *
            ((N:ℝ) / ((d:ℝ) * log ((N:ℝ)^(1/2-δ)/d)) *
              (epsilon * wuLocalExponent k δ)) := by dsimp only [w]; ring
        _ ≤ (convolutionCoeff W d : ℝ) * (epsilon * ((N:ℝ)/log N) / d) :=
          mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [← mul_sum]; rfl

/-- Any fixed nonnegative density prefactor is absorbed before N and all boxes.
The varying singular series is preserved, and A=0 requires no cancellation. -/
theorem sourceClosedKMass_pair_theta (k : ℕ) {δ epsilon A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hA : 0 ≤ A) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        A * (wuSingularSeries N / log N) *
          |(sourceClosedKMass N δ Δ V p false + sourceClosedKMass N δ Δ V p true) -
            (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true)| ≤
        epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hAp : 0 < A+1 := by positivity
  have he' : 0 < epsilon/(A+1) := div_pos he hAp
  obtain ⟨T, hT4, hT⟩ := sourceClosedKMass_pair_uniform k hδ hδhi he'
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have hN4 := hT4.trans hN
  let W := convolutionWuWindows N Δ V
  let Theta := boxTheta N ((N:ℝ)^(1/2-δ)) W
  let X := wuSingularSeries N / log N * ((N:ℝ)/log N) *
    boxConvolutionReciprocalMass W
  have hlog : 0 < log (N:ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hpay : X ≤ Theta/2 := HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb
  have hTheta : 0 ≤ Theta := by linarith
  have hbudget : A * (epsilon/(A+1)) ≤ epsilon := by
    rw [← mul_div_assoc, div_le_iff₀ hAp]
    nlinarith
  calc
    _ ≤ A * (wuSingularSeries N / log N) *
        ((epsilon/(A+1)) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass W) :=
      mul_le_mul_of_nonneg_left (hT N hN i Δ V hb p hp hs)
        (mul_nonneg hA (div_nonneg hC hlog.le))
    _ = (A * (epsilon/(A+1))) * X := by dsimp only [X]; ring
    _ ≤ (A * (epsilon/(A+1))) * (Theta/2) :=
      mul_le_mul_of_nonneg_left hpay (mul_nonneg hA he'.le)
    _ ≤ epsilon * (Theta/2) := mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ ≤ epsilon * Theta := mul_le_mul_of_nonneg_left (by linarith) he.le

end Wu2008DoubleSieve.HighNonunit
