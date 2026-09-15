import Wu18938Campaign.M1.Confirmed.OmegaGeometry
import Wu18938Campaign.M1.Confirmed.RelativeErrors
import MathlibNt.Wu2008DoubleSieve.Omega3SieveSource

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Omega

open Wu2008DoubleSieve Finset Real Filter
open scoped Classical Topology

theorem R1_log_saving (m : ℕ) {η δ A : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ s t Z
        (convolutionWuWindows N Δ V) ≤ C * N / log (N : ℝ) ^ A := by
  let F := (max 1 (1 / (η / 10))) ^ (m + 2)
  obtain ⟨C,hC,T,hT4,hT⟩ := omega3_balanced_interval_distribution A (η / 10) F
    hA (by positivity) (by positivity) hδ
  refine ⟨(⌈F⌉₊ + 1 : ℝ) * C,by positivity,T,hT4,?_⟩
  intro N hN i Δ V hb s t hs hst ht Z
  let W := convolutionWuWindows N Δ V
  let L := omega3CofactorLabels N δ s t W
  have hlay := layers hb (by omega) hη hδ hs hst ht
  have hj (j : ℕ) :
      (∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
        (3 : ℝ) ^ q.primeFactors.card *
          |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
            omega3LayerCoefficient W L j e *
              omega3ProfileError N q e (omega3LayerLower L j e)
                (omega3LayerUpper N δ s L j e)|) ≤ C * N / log (N : ℝ) ^ A := by
    apply hT N hN (omega3LayerSupport L j) (omega3LayerCoefficient W L j)
      (omega3LayerLower L j) (omega3LayerUpper N δ s L j)
    · intro e he
      have hc := omega3LayerLabel_mem he
      have hg := profile hb (by omega) hη hδ hs hst ht hc.1
      exact hc.2 ▸ ⟨hg.2.2.1,hg.2.2.2.1⟩
    · intro e _
      exact hlay.2 j e
    · intro e he
      have hc := omega3LayerLabel_mem he
      have hg := profile hb (by omega) hη hδ hs hst ht hc.1
      refine ⟨omega3LayerLower_two he,?_,?_⟩
      · simpa only [omega3LayerLower,omega3LayerUpper,hc.2] using hg.2.2.2.2.1
      · simpa only [omega3LayerUpper,hc.2] using hg.2.2.2.2.2
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ ∑ j ∈ range ⌈F⌉₊,
        ∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
          (3 : ℝ) ^ q.primeFactors.card *
            |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
              omega3LayerCoefficient W L j e *
                omega3ProfileError N q e (omega3LayerLower L j e)
                  (omega3LayerUpper N δ s L j e)| :=
      omega3SieveR1_le_layers W hlay.1
        (fun _ hc => (profile hb (by omega) hη hδ hs hst ht hc).1)
    _ ≤ ∑ _j ∈ range ⌈F⌉₊, C * N / log (N : ℝ) ^ A := sum_le_sum (fun j _ => hj j)
    _ = (⌈F⌉₊ : ℝ) * (C * N / log (N : ℝ) ^ A) := by simp
    _ ≤ (⌈F⌉₊ + 1 : ℝ) * (C * N / log (N : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem R1_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ s t Z
        (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C,hC,T1,hT14,h1⟩ := R1_log_saving m hη hδ (by positivity : (0 : ℝ) < (5 * m + 3 : ℕ))
  obtain ⟨c,hc,T2,_,hTheta⟩ := roughBox_theta_lower m hη hδ
  obtain ⟨T3,hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb s t hs hst ht Z
  have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  have hr := h1 N (by omega) i Δ V hb s t hs hst ht Z
  rw [rpow_natCast] at hr
  have htheta := hTheta N (by omega) i Δ V hb
  have hbudget : C / log (N : ℝ) ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos he hc)).mp (hlogT N (by omega))
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C * N / log (N : ℝ) ^ (5 * m + 3) := hr
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by
      rw [show 5 * m + 3 = (5 * m + 2) + 1 by omega,pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta he.le

theorem R2_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ s t
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let F := (max 1 (1 / (η / 10))) ^ (m + 2)
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨C,hC,hbound⟩ := omega3_non_coprime_euler_bound
  obtain ⟨T0,hT04,hpay⟩ := roughBox_absolute_power_relative m 5 hη hδ he
    (show 0 < 2 * C * F / log 2 by positivity) (show 0 < η / 10 by positivity)
  obtain ⟨T1,hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hlog1 := hlogT N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have h := hbound N (by omega) i δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
    ((N : ℝ) ^ (η / 10)) F (convolutionWuWindows N Δ V)
    (omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
      (sqrt ((N : ℝ) ^ (1 / 2 - δ)))) hg.2.2.2.1
    (rpow_pos_of_pos hNpos _) hF.le (filter_subset _ _) (by
      intro q hq
      have hqd := (omega3SieveModuli_properties hq).2.2.2
      have hDN := hg.2.2.2.2.2.2.1
      omega) (by
      intro c hc
      have hp := profile hb (by omega) hη hδ hs hst ht hc
      exact ⟨hp.1,hp.2.1,cofactor_rough hb (by omega) hη hδ hs hst ht hc⟩)
    (fibre hb (by omega) hη hδ hs hst ht)
  calc
    _ ≤ C * F * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ (η / 10) * log 2)) := h
    _ ≤ C * F * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ (η / 10) * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * F / log 2) * N * log N ^ 5 / (N : ℝ) ^ (η / 10) := by ring
    _ ≤ _ := hpay N (by omega) i Δ V hb

theorem switched_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SwitchedSiftedCount N δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
        (convolutionWuWindows N Δ V) ≤
      omega3SieveX N δ s t (convolutionWuWindows N Δ V) *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := omega3_switched_upper_source_density hδ hδhi hρ
  obtain ⟨T1,_,h1⟩ := R1_relative m hη hδ (half_pos he)
  obtain ⟨T2,_,h2⟩ := R2_relative m hη hδ hδhi (half_pos he)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hd := (omega3_switched_sifted_le_closed N δ s t _ (convolutionWuWindows N Δ V)
    (fun _ hd => hb.support_pos hd)).trans (h0 N (by omega) heven i s t _)
  have hr := h1 N (by omega) i Δ V hb s t hs hst ht (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  have he' := h2 N (by omega) i Δ V hb s t hs hst ht
  linarith only [hd,hr,he']

end Wu18938Campaign.M1.Confirmed.Omega
