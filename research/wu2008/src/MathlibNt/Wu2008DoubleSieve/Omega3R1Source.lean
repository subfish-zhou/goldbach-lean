import MathlibNt.Wu2008DoubleSieve.Omega3R1Distribution

/-!
# Payment of the actual switched R1

Wu (2004), (5.7), with the false uniqueness claim replaced by the proved
fixed common layers. Raw layer coefficients use the fixed bound C(k,delta).
The saving 5*k+3 pays the original Theta lower scale 5*k+2.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem omega3LayerLower_two {i N j e : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ}
    (he : e ∈ omega3LayerSupport (omega3CofactorLabels N δ s t W) j) :
    2 ≤ omega3LayerLower (omega3CofactorLabels N δ s t W) j e := by
  have hlabel := (omega3LayerLabel_mem he).1
  have hp := (mem_primeWindow.mp (mem_omega3CofactorLabels.mp hlabel).2.1).1
  unfold omega3LayerLower
  exact_mod_cast hp.two_le

/-- Arbitrary fixed logarithmic saving, uniformly before all actual boxes,
layers and cutoffs. Evenness is not needed for this AP remainder. -/
theorem omega3_sieve_R1_log_saving (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SieveR1 N (⌊Q⌋₊ + 1) δ s t (sqrt Q) W ≤
          C * N / log (N : ℝ) ^ A := by
  have hη : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨C, hC, T1, hT14, hT1⟩ := omega3_balanced_interval_distribution A
    (wuLocalExponent k δ / 10) (omega3LayerConstant k δ)
    hA hη (omega3LayerConstant_pos k δ).le hδ
  obtain ⟨T2, _, hT2⟩ := omega3_cofactor_common_profile_layers k hδ hδhi
  obtain ⟨T3, _, hT3⟩ := omega3_source_R1_le_common_profiles k hδ hδhi
  refine ⟨((omega3LayerCount k δ : ℝ) + 1) * C, by positivity,
    max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  let W := convolutionWuWindows N Δ V
  let L := omega3CofactorLabels N δ s t W
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  obtain ⟨_, hcoeff, hgeom, _, _⟩ := hT2 N hN2 i Δ V hb s t hs hst ht
  have hj : ∀ j : ℕ,
      (∑ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q),
        (3 : ℝ) ^ q.primeFactors.card *
          |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
            omega3LayerCoefficient W L j e *
              omega3ProfileError N q e (omega3LayerLower L j e)
                (omega3LayerUpper N δ s L j e)|) ≤ C * N / log (N : ℝ) ^ A := by
    intro j
    apply hT1 N hN1 (omega3LayerSupport L j) (omega3LayerCoefficient W L j)
      (omega3LayerLower L j) (omega3LayerUpper N δ s L j)
    · intro e he
      obtain ⟨_, _, _, hlo, hhi, _⟩ := hgeom j e he
      exact ⟨hlo, hhi⟩
    · intro e _
      rw [abs_of_nonneg (hcoeff j e).1]
      exact (hcoeff j e).2.1
    · intro e he
      obtain ⟨_, _, _, _, _, _, hab, _, _, hupper⟩ := hgeom j e he
      exact ⟨omega3LayerLower_two he, hab, hupper⟩
  have hlog : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by have := hT14.trans hN1; omega))
  calc
    _ ≤ ∑ j ∈ range (omega3LayerCount k δ),
        ∑ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q),
          (3 : ℝ) ^ q.primeFactors.card *
            |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
              omega3LayerCoefficient W L j e *
                omega3ProfileError N q e (omega3LayerLower L j e)
                  (omega3LayerUpper N δ s L j e)| :=
      hT3 N hN3 i Δ V hb s t hs hst ht _ _
    _ ≤ ∑ _j ∈ range (omega3LayerCount k δ), C * N / log (N : ℝ) ^ A :=
      sum_le_sum (fun j _ => hj j)
    _ = (omega3LayerCount k δ : ℝ) * (C * N / log (N : ℝ) ^ A) := by
      simp
    _ ≤ ((omega3LayerCount k δ : ℝ) + 1) * C * N / log (N : ℝ) ^ A := by
      calc
        _ ≤ ((omega3LayerCount k δ : ℝ) + 1) * (C * N / log (N : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

/-- All analytic and actual-source premises are discharged. One threshold
precedes every legal box; the original Theta is not replaced by N/log^2 N. -/
theorem omega3_sieve_R1_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SieveR1 N (⌊Q⌋₊ + 1) δ s t (sqrt Q) W ≤ ε * boxTheta N Q W := by
  obtain ⟨C, hC, T1, hT14, hR1⟩ := omega3_sieve_R1_log_saving k hδ hδhi
    (show (0 : ℝ) < (5 * k + 3 : ℕ) by positivity)
  obtain ⟨c, hc, T2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hlog : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by have := hT14.trans hN1; omega))
  have hB := hR1 N hN1 i Δ V hb s t hs hst ht
  dsimp only at hB ⊢
  rw [rpow_natCast] at hB
  have htheta := hTheta N hN2 i hb.1 Δ hb.2.1 hb.2.2.1 V
    hb.2.2.2.2.1 hb.2.2.2.2.2
  have hbudget : C / log N ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp (hT3 N hN3)
    nlinarith
  calc
    _ ≤ C * N / log N ^ (5 * k + 3) := hB
    _ = (C / log N) * ((N : ℝ) / log N ^ (5 * k + 2)) := by
      rw [show 5 * k + 3 = (5 * k + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log N ^ (5 * k + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log N ^ (5 * k + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

end Wu2008DoubleSieve
