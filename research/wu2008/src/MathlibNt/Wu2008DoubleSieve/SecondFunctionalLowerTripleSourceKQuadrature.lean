import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleClosedQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighKernelPayloads

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.LowerTripleSourceK
open Finset Real Filter LowerTripleContinuous
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Literal closed-prime payload at the supported d and its actual phi. -/
noncomputable def sourceClosedK (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  closedPrimeKj ((N:ℝ)^(1/2-δ)/d) (1/p.S) (1/p.kappa1) (1/p.kappa2)
    (1/p.kappa3) (1/p.s) j (omega3XPhi N d δ)

/-- The integral uses exactly the same phi, not the compactness cap. -/
noncomputable def sourceIntegralK (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  K (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j (omega3XPhi N d δ)

/-- Original sigma and N/(d log R), without normalization by total mass. -/
noncomputable def closedKMass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ((N:ℝ)/(d * log ((N:ℝ)^(1/2-δ)/d))) * sourceClosedK N d δ p j

noncomputable def integralKMass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ((N:ℝ)/(d * log ((N:ℝ)^(1/2-δ)/d))) * sourceIntegralK N d δ p j

/-- The threshold precedes all boxes, supported d, mother parameters and labels. -/
theorem sourceClosedK_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), ∀ j : Fin 6,
        |sourceClosedK N d δ p j - sourceIntegralK N d δ p j| < epsilon := by
  let Phi := max 2 (1 / wuLocalExponent k δ)
  obtain ⟨R0, _, hR0⟩ := closedPrimeK_six_uniform Phi (le_max_left _ _) epsilon he
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
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  exact hR0 _ hlarge _ ⟨hphi, hg.2.2.2.trans (le_max_right _ _)⟩
    _ _ _ _ _ (mother_compact_parameters p hp hs)

/-- Original sigma-weighted error, using the actual supported log scale. -/
theorem closedKMass_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
        |closedKMass N δ Δ V p j - integralKMass N δ Δ V p j| ≤
        epsilon * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have heta := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT4, hT⟩ := sourceClosedK_uniform k hδ hδhi (mul_pos he heta)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs j
  have hN2 : 2 ≤ N := by omega
  let W := convolutionWuWindows N Δ V
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ) *
    ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d))
  let E := fun d => sourceClosedK N d δ p j - sourceIntegralK N d δ p j
  have hid : closedKMass N δ Δ V p j - integralKMass N δ Δ V p j =
      ∑ d ∈ boxConvolutionSupport W, w d * E d := by
    unfold closedKMass integralKMass
    rw [← sum_sub_distrib]
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
        (hT N hN i Δ V hb p hp hs d hd j).le
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

/-- Six words share one budget; internally the prime tolerance is epsilon*nu/6. -/
theorem closedKMass_six_abs_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        (∀ j : Fin 6,
          |closedKMass N δ Δ V p j - integralKMass N δ Δ V p j| ≤
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
        (∑ j : Fin 6, |closedKMass N δ Δ V p j - integralKMass N δ Δ V p j|) ≤
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ∧
        |(∑ j : Fin 6, closedKMass N δ Δ V p j) -
          (∑ j : Fin 6, integralKMass N δ Δ V p j)| ≤
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := closedKMass_uniform k hδ hδhi
    (show 0 < epsilon/6 by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have h := hT N hN i Δ V hb p hp hs
  have hsum : (∑ j : Fin 6,
      |closedKMass N δ Δ V p j - integralKMass N δ Δ V p j|) ≤
      epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ ∑ _j : Fin 6, (epsilon/6) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
        sum_le_sum fun j _ => h j
      _ = _ := by simp; ring
  refine ⟨fun j => (single_le_sum (fun _ _ => abs_nonneg _) (mem_univ j)).trans hsum,
    hsum, ?_⟩
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans hsum

/-- Requested one-sided terminals, with the unchanged actual-phi integral main. -/
theorem closedKMass_six_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        (∀ j : Fin 6, closedKMass N δ Δ V p j ≤ integralKMass N δ Δ V p j +
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
        (∑ j : Fin 6, closedKMass N δ Δ V p j) ≤
          (∑ j : Fin 6, integralKMass N δ Δ V p j) +
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := closedKMass_six_abs_uniform k hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb p hp hs
  obtain ⟨hj,_,ha⟩ := hT N hN i Δ V hb p hp hs
  exact ⟨fun j => sub_le_iff_le_add'.mp ((le_abs_self _).trans (hj j)),
    sub_le_iff_le_add'.mp ((le_abs_self _).trans ha)⟩

end Wu2008DoubleSieve.LowerTripleSourceK
