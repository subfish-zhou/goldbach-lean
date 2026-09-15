import MathlibNt.Wu2008DoubleSieve.ClassicalPairErrorPayment
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-! The original physical seventh/eighth sieve, with every additive error
paid and the global-N coefficient eight. The threshold precedes every
geometric pair family; no main-mass estimate or integral is assumed. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real Filter
open scoped Classical Topology

noncomputable def classicalDensityCoefficient (δ ρ : ℝ) : ℝ :=
  (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))

/-- The existing signed aggregate is consumed, not replaced by rowwise errors. -/
theorem classicalR1_error_paid {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ S : Finset (ℕ × ℕ),
      ClassicalPairGeometry N S → ∀ Z : ℝ,
      classicalPairR1 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨C, hC, T1, _, hR1⟩ := classicalPair_balanced_distribution 3 (by norm_num) hδ
  obtain ⟨T2, hT2, hpay⟩ := ninth_log_cube_error_budget hC hε
  refine ⟨max T1 T2, hT2.trans (le_max_right _ _), ?_⟩
  intro N hN S hS Z
  have h := hR1 N ((le_max_left _ _).trans hN) S hS Z
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast] at h
  exact h.trans (hpay N ((le_max_right _ _).trans hN))

theorem classical_all_errors_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ S : Finset (ℕ × ℕ),
      ClassicalPairGeometry N S →
      classicalPairR1 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        classicalR2 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        classicalSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
          ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨T1, hT1, h1⟩ := classicalR1_error_paid hδ (show 0 < ε / 3 by positivity)
  obtain ⟨T2, _, h2⟩ := classicalR2_error_paid (show 0 < ε / 3 by positivity)
  obtain ⟨T3, _, h3⟩ := classicalSmall_error_paid (show 0 < ε / 3 by positivity)
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN S hS
  have hp1 := h1 N ((le_max_left _ _).trans hN) S hS (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  have hp2 := h2 N ((le_max_left T2 T3).trans ((le_max_right _ _).trans hN)) S hS δ hδ hδhi
  have hp3 := h3 N ((le_max_right T2 T3).trans ((le_max_right _ _).trans hN)) δ hδ
  calc
    _ ≤ ε / 3 * N / log N ^ 2 + ε / 3 * N / log N ^ 2 +
        ε / 3 * N / log N ^ 2 := add_le_add (add_le_add hp1 hp2) hp3
    _ = _ := by ring

/-- The coefficient comes from global-N Rosser density, not the local
length N/(ab). The density slack multiplies actual classicalMass. -/
theorem classicalPhysical_source_density {δ ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), ClassicalPairGeometry N S →
      ((physical N S).card : ℝ) ≤
        (classicalDensityCoefficient δ ρ * wuSingularSeries N / log N) * classicalMass N S +
        classicalPairR1 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        classicalR2 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        classicalSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by
  obtain ⟨T, _, hT⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN he S hS
  have hN512 := (le_max_right T 512).trans hN
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hf := classicalPhysical_upper_finite (by omega) hS he
    (sqrt ((N : ℝ) ^ (1 / 2 - δ))) hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hd := mul_le_mul_of_nonneg_left
    (hT N ((le_max_left _ _).trans hN) he) (classicalMass_nonneg N S)
  change classicalMass N S * _ ≤ classicalMass N S *
    (classicalDensityCoefficient δ ρ * wuSingularSeries N / log N) at hd
  calc
    _ ≤ classicalMass N S *
        (classicalDensityCoefficient δ ρ * wuSingularSeries N / log N) +
        classicalPairR1 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        classicalR2 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        classicalSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by linarith
    _ = _ := by ring

/-- Fully error-paid fixed-delta source; only genuine geometric hypotheses. -/
theorem classicalPhysical_source_error_paid {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), ClassicalPairGeometry N S →
      ((physical N S).card : ℝ) ≤
        (classicalDensityCoefficient δ ρ * wuSingularSeries N / log N) * classicalMass N S +
          ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨T1, hT1, hu⟩ := classicalPhysical_source_density hδ hδhi hρ
  obtain ⟨T2, _, he⟩ := classical_all_errors_paid hδ hδhi hε
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN heven S hS
  have hupper := hu N ((le_max_left _ _).trans hN) heven S hS
  have herror := he N ((le_max_right _ _).trans hN) S hS
  linarith

/-- Delta is fixed from epsilon before any threshold; it is not swallowed
by letting N grow with a fixed positive loss. No positivity of J7/J8 is used. -/
theorem classical_density_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 2 ∧ classicalDensityCoefficient d d ≤ 8 + ε := by
  have hf : ContinuousAt (fun d => classicalDensityCoefficient d d) 0 := by
    unfold classicalDensityCoefficient
    fun_prop (disch := norm_num)
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp hf ε hε
  let d := min (r / 2) (1 / 20)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdr : d < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd20 : d ≤ 1 / 20 := min_le_right _ _
  have hdist : dist d 0 < r := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hd] using hdr
  have h := (abs_lt.mp (show |classicalDensityCoefficient d d - classicalDensityCoefficient 0 0| < ε by
    simpa only [Real.dist_eq] using hfr hdist)).2
  refine ⟨d, hd, by linarith, ?_⟩
  norm_num [classicalDensityCoefficient] at h
  unfold classicalDensityCoefficient
  linarith

/-- The complete epsilon-only bounding-sieve endpoint. Uniformity is
stronger than required: T precedes every original-alpha geometric support. -/
theorem classicalPhysical_upper_coefficient_eight {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), ClassicalPairGeometry N S →
      ((physical N S).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * classicalMass N S +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hc : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨d, hd, hdhi, hcoef⟩ := classical_density_parameters hε
  obtain ⟨T, hT, hupper⟩ := classicalPhysical_source_error_paid hd hdhi hd
    (show 0 < ε * wuSingularSeries 1 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN he S hS
  have hNp : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N hNp
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hNp (one_dvd N)
  have hmain :
      (classicalDensityCoefficient d d * wuSingularSeries N / log N) * classicalMass N S ≤
      ((8 + ε) * wuSingularSeries N / log N) * classicalMass N S := by
    apply mul_le_mul_of_nonneg_right _ (classicalMass_nonneg N S)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hC.le) hlog.le
  have herr : (ε * wuSingularSeries 1) * N / log N ^ (2 : ℕ) ≤
      ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by gcongr
  exact (hupper N hN he S hS).trans (add_le_add hmain herr)

/-- Literal original carriers, no caller-supplied count, density, R1, R2,
small-output, coprimality or main-mass premises. Both families share T. -/
theorem seventh_eighth_physical_upper_classicalMass {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((physicalT7 N).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * classicalMass N (seventhPairs N) +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ∧
      ((physicalT8 N).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * classicalMass N (eighthPairs N) +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T, hT, hu⟩ := classicalPhysical_upper_coefficient_eight hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  exact ⟨hu N hN he _ (seventh_classicalPairGeometry (hT.trans hN)),
    hu N hN he _ (eighth_classicalPairGeometry (hT.trans hN))⟩

/-- Original pair coprimality is internal source data. It was not needed
by the stronger generic sieve and is never extended to r or its output. -/
theorem seventh_eighth_pair_coprime (N : ℕ) :
    (∀ p ∈ seventhPairs N, p.1.Coprime N ∧ p.2.Coprime N) ∧
    (∀ p ∈ eighthPairs N, p.1.Coprime N ∧ p.2.Coprime N) := by
  constructor
  · intro p hp
    obtain ⟨_, _, ha, hb, _⟩ := lowerPairs_data (mem_filter.mp hp).1
    exact ⟨ha, hb⟩
  · intro p hp
    obtain ⟨_, _, ha, hb, _⟩ := lowerPairs_data (mem_filter.mp hp).1
    exact ⟨ha, hb⟩
end Wu2008DoubleSieve.SeventhEighth
