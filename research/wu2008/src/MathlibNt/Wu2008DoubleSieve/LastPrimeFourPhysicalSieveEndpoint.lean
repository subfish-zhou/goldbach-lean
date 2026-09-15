import MathlibNt.Wu2008DoubleSieve.LastPrimeFourSmallOutput
import MathlibNt.Wu2008DoubleSieve.LastPrimeFourRawMassBridge
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-! The original physical tenth/eleventh sieve, with every additive error
paid and the global-N coefficient eight. The threshold precedes every
original family; no main-mass estimate or integral is assumed. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real Filter
open scoped Classical Topology

noncomputable def fourDensityCoefficient (δ ρ : ℝ) : ℝ :=
  (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))

/-- The existing signed aggregate is consumed, not replaced by rowwise errors. -/
theorem fourR1_error_paid {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, ∀ Z : ℝ,
      signedR1 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨C₀, hC₀, T1, _, hR⟩ := both_signed_aggregate_distribution 3 (by norm_num) hδ
  let C : ℝ := ((layerBound : ℝ)+1)*C₀
  have hC : 0 < C := by positivity
  have hR1 := hR
  obtain ⟨T2, hT2, hpay⟩ := ninth_log_cube_error_budget hC hε
  refine ⟨max T1 T2, hT2.trans (le_max_right _ _), ?_⟩
  intro N hN e Z
  have h := hR1 N ((le_max_left _ _).trans hN) e Z
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast] at h
  exact h.trans (hpay N ((le_max_right _ _).trans hN))

theorem four_all_errors_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool,
      signedR1 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        fourR2 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        fourSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
          ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨T1, hT1, h1⟩ := fourR1_error_paid hδ (show 0 < ε / 3 by positivity)
  obtain ⟨T2, _, h2⟩ := fourR2_error_paid (show 0 < ε / 3 by positivity)
  obtain ⟨T3, _, h3⟩ := fourSmall_error_paid (show 0 < ε / 3 by positivity)
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN e
  have hp1 := h1 N ((le_max_left _ _).trans hN) e (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  have hp2 := h2 N ((le_max_left T2 T3).trans ((le_max_right _ _).trans hN)) e δ hδ hδhi
  have hp3 := h3 N ((le_max_right T2 T3).trans ((le_max_right _ _).trans hN)) δ hδ
  calc
    _ ≤ ε / 3 * N / log N ^ 2 + ε / 3 * N / log N ^ 2 +
        ε / 3 * N / log N ^ 2 := add_le_add (add_le_add hp1 hp2) hp3
    _ = _ := by ring

/-- The coefficient comes from global-N Rosser density, not the local
length N/(abc*n). The density slack multiplies actual fourMass. -/
theorem fourPhysical_source_density {δ ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ e : Bool,
      ((original N e).card : ℝ) ≤
        (fourDensityCoefficient δ ρ * wuSingularSeries N / log N) * fourMass N e +
        signedR1 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        fourR2 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        fourSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by
  obtain ⟨T, _, hT⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN he e
  have hN512 := (le_max_right T 512).trans hN
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hf := fourPhysical_upper_finite (by omega) e he
    (sqrt ((N : ℝ) ^ (1 / 2 - δ))) hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hd := mul_le_mul_of_nonneg_left
    (hT N ((le_max_left _ _).trans hN) he) (fourMass_nonneg N e)
  change fourMass N e * _ ≤ fourMass N e *
    (fourDensityCoefficient δ ρ * wuSingularSeries N / log N) at hd
  calc
    _ ≤ fourMass N e *
        (fourDensityCoefficient δ ρ * wuSingularSeries N / log N) +
        signedR1 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        fourR2 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        fourSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by linarith
    _ = _ := by ring

/-- Fully error-paid fixed-delta source for both literal original families. -/
theorem fourPhysical_source_error_paid {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ e : Bool,
      ((original N e).card : ℝ) ≤
        (fourDensityCoefficient δ ρ * wuSingularSeries N / log N) * fourMass N e +
          ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨T1, hT1, hu⟩ := fourPhysical_source_density hδ hδhi hρ
  obtain ⟨T2, _, he⟩ := four_all_errors_paid hδ hδhi hε
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN heven e
  have hupper := hu N ((le_max_left _ _).trans hN) heven e
  have herror := he N ((le_max_right _ _).trans hN) e
  linarith

/-- Delta is fixed from epsilon before any threshold; it is not swallowed
by letting N grow with a fixed positive loss. No integral positivity is used. -/
theorem four_density_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 2 ∧ fourDensityCoefficient d d ≤ 8 + ε := by
  have hf : ContinuousAt (fun d => fourDensityCoefficient d d) 0 := by
    unfold fourDensityCoefficient
    fun_prop (disch := norm_num)
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp hf ε hε
  let d := min (r / 2) (1 / 20)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdr : d < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd20 : d ≤ 1 / 20 := min_le_right _ _
  have hdist : dist d 0 < r := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hd] using hdr
  have h := (abs_lt.mp (show |fourDensityCoefficient d d - fourDensityCoefficient 0 0| < ε by
    simpa only [Real.dist_eq] using hfr hdist)).2
  refine ⟨d, hd, by linarith, ?_⟩
  norm_num [fourDensityCoefficient] at h
  unfold fourDensityCoefficient
  linarith

/-- The complete epsilon-only bounding-sieve endpoint. The common threshold
precedes the choice of either literal original family. -/
theorem fourPhysical_upper_coefficient_eight {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ e : Bool,
      ((original N e).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * fourMass N e +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hc : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨d, hd, hdhi, hcoef⟩ := four_density_parameters hε
  obtain ⟨T, hT, hupper⟩ := fourPhysical_source_error_paid hd hdhi hd
    (show 0 < ε * wuSingularSeries 1 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN he e
  have hNp : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N hNp
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hNp (one_dvd N)
  have hmain :
      (fourDensityCoefficient d d * wuSingularSeries N / log N) * fourMass N e ≤
      ((8 + ε) * wuSingularSeries N / log N) * fourMass N e := by
    apply mul_le_mul_of_nonneg_right _ (fourMass_nonneg N e)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hC.le) hlog.le
  have herr : (ε * wuSingularSeries 1) * N / log N ^ (2 : ℕ) ≤
      ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by gcongr
  exact (hupper N hN he e).trans (add_le_add hmain herr)

/-- The full five-label mass bridge is consumed after the sieve and error budget. -/
theorem fourPhysical_upper_rawMass {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ e : Bool,
      ((original N e).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * fourRawMass N e +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T,hT,hu⟩ := fourPhysical_upper_coefficient_eight hε
  refine ⟨T,hT,?_⟩
  intro N hN he e
  have hNp : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N hNp
  have hcoef : 0 ≤ (8 + ε) * wuSingularSeries N / log N := by positivity
  exact (hu N hN he e).trans (add_le_add
    (mul_le_mul_of_nonneg_left (fourMass_le_rawMass N e) hcoef) le_rfl)

/-- Literal epsilon-only endpoint, with one threshold for both original families. -/
theorem physical10_physical11_upper_rawMass {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((TruncatedFourPhysical.Physical10 N).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * FourRoughClosedMass.rawMass10 N +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ∧
      ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤
        ((8 + ε) * wuSingularSeries N / log N) * FourRoughClosedMass.rawMass11 N +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T,hT,hu⟩ := fourPhysical_upper_rawMass hε
  exact ⟨T,hT,fun N hN he => ⟨hu N hN he false,hu N hN he true⟩⟩

end Wu2008DoubleSieve.LastPrimeFour
